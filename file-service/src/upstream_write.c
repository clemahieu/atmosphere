/* Stock liblmdb writer. Linked against the reference objects, not the shim. */
#include <stdio.h>
#include <stdlib.h>
#include "lmdb.h"

int main(int argc, char **argv)
{
	MDB_env *env = NULL;
	MDB_txn *txn = NULL;
	MDB_dbi dbi;
	MDB_val key, val;
	unsigned long long mapsize;
	int rc;

	if (argc != 3) {
		fprintf(stderr, "usage: upstream_write path mapsize\n");
		return 1;
	}
	mapsize = strtoull(argv[2], NULL, 10);
	rc = mdb_env_create(&env);
	if (rc) {
		fprintf(stderr, "create: %s\n", mdb_strerror(rc));
		return 1;
	}
	rc = mdb_env_set_mapsize(env, (mdb_size_t)mapsize);
	if (rc) {
		fprintf(stderr, "set_mapsize: %s\n", mdb_strerror(rc));
		return 1;
	}
	rc = mdb_env_open(env, argv[1], MDB_NOSUBDIR | MDB_NOTLS | MDB_NORDAHEAD, 0644);
	if (rc) {
		fprintf(stderr, "open: %s\n", mdb_strerror(rc));
		mdb_env_close(env);
		return 1;
	}
	rc = mdb_txn_begin(env, NULL, 0, &txn);
	if (rc) {
		fprintf(stderr, "begin: %s\n", mdb_strerror(rc));
		mdb_env_close(env);
		return 1;
	}
	rc = mdb_dbi_open(txn, NULL, 0, &dbi);
	if (rc) {
		fprintf(stderr, "dbi: %s\n", mdb_strerror(rc));
		mdb_txn_abort(txn);
		mdb_env_close(env);
		return 1;
	}
	key.mv_data = "kite";
	key.mv_size = 4;
	val.mv_data = "hawk";
	val.mv_size = 4;
	rc = mdb_put(txn, dbi, &key, &val, 0);
	if (rc) {
		fprintf(stderr, "put: %s\n", mdb_strerror(rc));
		mdb_txn_abort(txn);
		mdb_env_close(env);
		return 1;
	}
	rc = mdb_txn_commit(txn);
	if (rc) {
		fprintf(stderr, "commit: %s\n", mdb_strerror(rc));
		mdb_env_close(env);
		return 1;
	}
	mdb_env_close(env);
	printf("upstream wrote kite=hawk\n");
	return 0;
}
