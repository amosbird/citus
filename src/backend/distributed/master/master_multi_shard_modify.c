/*-------------------------------------------------------------------------
 *
 * master_multi_shard_modify.c
 *	  UDF to run multi shard update/delete queries
 *
 * This file contains master_multi_shard_modify function, which takes a update
 * or delete query and runs it on shards. The distributed modify operation can
 * be done within a distributed transaction and commited in one-phase or
 * two-phase fashion.
 *
 * Copyright (c) 2012-2016, Citus Data, Inc.
 *-------------------------------------------------------------------------
 */


#include "postgres.h"
#include "funcapi.h"
#include "libpq-fe.h"
#include "miscadmin.h"

#include "access/xact.h"
#include "catalog/namespace.h"
#include "catalog/pg_class.h"
#include "commands/dbcommands.h"
#include "commands/event_trigger.h"
#include "distributed/citus_ruleutils.h"
#include "distributed/connection_cache.h"
#include "distributed/master_metadata_utility.h"
#include "distributed/master_protocol.h"
#include "distributed/metadata_cache.h"
#include "distributed/multi_client_executor.h"
#include "distributed/multi_physical_planner.h"
#include "distributed/multi_router_planner.h"
#include "distributed/multi_server_executor.h"
#include "distributed/multi_transaction.h"
#include "distributed/pg_dist_shard.h"
#include "distributed/pg_dist_partition.h"
#include "distributed/resource_lock.h"
#include "distributed/worker_protocol.h"
#include "optimizer/clauses.h"
#include "optimizer/predtest.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/var.h"
#include "nodes/makefuncs.h"
#include "tcop/tcopprot.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"


static int SendQueryToShards(Query *query, List *shardIntervalList);
static HTAB * OpenConnectionsToAllShardPlacements(List *shardIntervalList);
static void OpenConnectionsToShardPlacements(uint64 shardId, HTAB *shardConnectionHash);

static int SendQueryToConnections(char *shardQueryString,
								  ShardConnections *shardConnections);

PG_FUNCTION_INFO_V1(master_multi_shard_modify);


/*
 * master_multi_shard_modify takes in a delete query string and pushes the
 * query to shards. It finds shards that match the criteria defined in the
 * delete command, generates the same delete query string for each of the
 * found shards with distributed table name replaced with the shard name and
 * sends the queries to the workers. It uses one-phase or two-phase commit
 * transactions depending on citus.copy_transaction_manager value.
 */
Datum
master_multi_shard_modify(PG_FUNCTION_ARGS)
{
	text *queryText = PG_GETARG_TEXT_P(0);
	char *queryString = text_to_cstring(queryText);
	List *queryTreeList = NIL;
	Oid relationId = InvalidOid;
	Index tableId = 1;
	DeleteStmt *deleteStatement = NULL;
	Query *deleteQuery = NULL;
	Node *queryTreeNode;
	List *restrictClauseList = NIL;
	bool isTopLevel = true;
	bool failOK = false;
	List *shardIntervalList = NIL;
	List *prunedShardIntervalList = NIL;
	int32 affectedTupleCount = 0;

	PreventTransactionChain(isTopLevel, "master_multi_shard_modify");

	queryTreeNode = ParseTreeNode(queryString);
	if (!IsA(queryTreeNode, DeleteStmt))
	{
		ereport(ERROR, (errmsg("query \"%s\" is not a delete statement",
							   queryString)));
	}

	deleteStatement = (DeleteStmt *) queryTreeNode;
	relationId = RangeVarGetRelid(deleteStatement->relation, NoLock, failOK);

	CheckDistributedTable(relationId);

	queryTreeList = pg_analyze_and_rewrite(queryTreeNode, queryString, NULL, 0);
	deleteQuery = (Query *) linitial(queryTreeList);

	ErrorIfModifyQueryNotSupported(deleteQuery);

	shardIntervalList = LoadShardIntervalList(relationId);
	restrictClauseList = WhereClauseList(deleteQuery->jointree);

	prunedShardIntervalList =
		PruneShardList(relationId, tableId, restrictClauseList, shardIntervalList);

	LockShards(prunedShardIntervalList);

	affectedTupleCount = SendQueryToShards(deleteQuery, prunedShardIntervalList);

	PG_RETURN_INT32(affectedTupleCount);
}


/*
 * SendQueryToShards executes the given query in all placements of the given
 * shard list and returns the total affected tuple count. The execution is done
 * in a distributed transaction and the commit protocol is decided according to
 * the value of citus.multi_shard_commit_protocol parameter. SendQueryToShards
 * does not acquire locks for the shards so it is advised to acquire locks to
 * the shards when necessary.
 */
static int
SendQueryToShards(Query *query, List *shardIntervalList)
{
	int affectedTupleCount = 0;
	HTAB *shardConnectionHash = OpenConnectionsToAllShardPlacements(shardIntervalList);
	List *allShardsConnectionList = ConnectionList(shardConnectionHash);

	PG_TRY();
	{
		ListCell *shardIntervalCell = NULL;

		foreach(shardIntervalCell, shardIntervalList)
		{
			ShardInterval *shardInterval = (ShardInterval *) lfirst(
				shardIntervalCell);
			Oid relationId = shardInterval->relationId;
			uint64 shardId = shardInterval->shardId;
			bool shardConnectionsFound = false;
			ShardConnections *shardConnections = NULL;
			StringInfo shardQueryString = makeStringInfo();
			char *shardQueryStringData = NULL;
			int shardAffectedTupleCount = -1;

			shardConnections = GetShardConnections(shardConnectionHash,
												   shardId,
												   &shardConnectionsFound);
			Assert(shardConnectionsFound);

			deparse_shard_query(query, relationId, shardId, shardQueryString);
			shardQueryStringData = shardQueryString->data;
			shardAffectedTupleCount = SendQueryToConnections(shardQueryStringData,
															 shardConnections);
			affectedTupleCount += shardAffectedTupleCount;
		}

		if (MultiShardCommitProtocol == COMMIT_PROTOCOL_2PC)
		{
			PrepareRemoteTransactions(allShardsConnectionList);
		}
	}
	PG_CATCH();
	{
		/* roll back all transactions */
		AbortRemoteTransactions(allShardsConnectionList);
		CloseConnections(allShardsConnectionList);

		PG_RE_THROW();
	}
	PG_END_TRY();

	CommitRemoteTransactions(allShardsConnectionList, false);

	return affectedTupleCount;
}


static HTAB *
OpenConnectionsToAllShardPlacements(List *shardIntervalList)
{
	HTAB *shardConnectionHash = CreateShardConnectionHash();

	ListCell *shardIntervalCell = NULL;

	foreach(shardIntervalCell, shardIntervalList)
	{
		ShardInterval *shardInterval = (ShardInterval *) lfirst(shardIntervalCell);
		uint64 shardId = shardInterval->shardId;

		OpenConnectionsToShardPlacements(shardId, shardConnectionHash);
	}

	return shardConnectionHash;
}


static void
OpenConnectionsToShardPlacements(uint64 shardId, HTAB *shardConnectionHash)
{
	bool shardConnectionsFound = false;

	/* get existing connections to the shard placements, if any */
	ShardConnections *shardConnections = GetShardConnections(shardConnectionHash,
															 shardId,
															 &shardConnectionsFound);

	List *shardPlacementList = FinalizedShardPlacementList(shardId);
	ListCell *shardPlacementCell = NULL;
	List *connectionList = NIL;

	Assert(!shardConnectionsFound);

	if (shardPlacementList == NIL)
	{
		ereport(ERROR, (errmsg("Could not find any shard placements for the shard "
							   UINT64_FORMAT, shardId)));
	}

	foreach(shardPlacementCell, shardPlacementList)
	{
		ShardPlacement *shardPlacement = (ShardPlacement *) lfirst(
			shardPlacementCell);
		char *workerName = shardPlacement->nodeName;
		uint32 workerPort = shardPlacement->nodePort;
		char *nodeUser = CurrentUserName();
		PGconn *connection = ConnectToNode(workerName, workerPort, nodeUser);
		TransactionConnection *transactionConnection = NULL;

		if (connection == NULL)
		{
			List *abortConnectionList = ConnectionList(shardConnectionHash);
			CloseConnections(abortConnectionList);

			ereport(ERROR, (errmsg("Could not establish a connection to all "
								   "placements.")));
		}

		transactionConnection = palloc0(sizeof(TransactionConnection));

		transactionConnection->connectionId = shardConnections->shardId;
		transactionConnection->transactionState = TRANSACTION_STATE_INVALID;
		transactionConnection->connection = connection;

		connectionList = lappend(connectionList, transactionConnection);
	}

	shardConnections->connectionList = connectionList;
}


/*
 * SendQueryToPlacement sends a query to all placement of a shard. Before the actual
 * query is sent,
 */
static int
SendQueryToConnections(char *shardQueryString, ShardConnections *shardConnections)
{
	uint64 shardId = shardConnections->shardId;
	List *connectionList = shardConnections->connectionList;
	ListCell *connectionCell = NULL;
	int32 shardAffectedTupleCount = -1;

	Assert(connectionList != NIL);

	foreach(connectionCell, connectionList)
	{
		TransactionConnection *transactionConnection =
			(TransactionConnection *) lfirst(connectionCell);
		PGconn *connection = transactionConnection->connection;
		PGresult *result = NULL;
		char *placementAffectedTupleString = NULL;
		int32 placementAffectedTupleCount = -1;

		/* send the query */
		result = PQexec(connection, "BEGIN");
		if (PQresultStatus(result) != PGRES_COMMAND_OK)
		{
			ReportRemoteError(connection, result);
			ereport(ERROR, (errmsg("Could not send query to shard placement.")));
		}

		result = PQexec(connection, shardQueryString);
		if (PQresultStatus(result) != PGRES_COMMAND_OK)
		{
			ReportRemoteError(connection, result);
			ereport(ERROR, (errmsg("Could not send query to shard placement.")));
		}

		placementAffectedTupleString = PQcmdTuples(result);
		placementAffectedTupleCount = pg_atoi(placementAffectedTupleString,
											  sizeof(int32), 0);

		if ((shardAffectedTupleCount == -1) ||
			(shardAffectedTupleCount == placementAffectedTupleCount))
		{
			shardAffectedTupleCount = placementAffectedTupleCount;
		}
		else
		{
			ereport(WARNING,
					(errmsg("modified %d tuples, but expected to modify %d",
							placementAffectedTupleCount, shardAffectedTupleCount),
					 errdetail("Affected tuple counts at placements of shard "
							   UINT64_FORMAT " are different.", shardId)));

			if (placementAffectedTupleCount > shardAffectedTupleCount)
			{
				shardAffectedTupleCount = placementAffectedTupleCount;
			}
		}

		PQclear(result);

		transactionConnection->transactionState = TRANSACTION_STATE_OPEN;
	}

	if (shardAffectedTupleCount == -1)
	{
		shardAffectedTupleCount = 0;
	}

	return shardAffectedTupleCount;
}
