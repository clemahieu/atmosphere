// SPDX-License-Identifier: MIT

/* The stat and dump tools reference the module loader. Encryption stays unbuilt. */
#include <stdio.h>
#include "lmdb.h"

void *mdb_modload(const char *file, const char *symname,
		MDB_crypto_funcs **mcf_ptr, char **errmsg)
{
	(void)file;
	(void)symname;
	(void)mcf_ptr;
	if (errmsg)
		*errmsg = "encryption modules are not built";
	return NULL;
}

void mdb_modunload(void *handle)
{
	(void)handle;
}

void mdb_modsetup(MDB_env *env, MDB_crypto_funcs *mcf, const char *passphrase)
{
	(void)env;
	(void)mcf;
	(void)passphrase;
	fprintf(stderr, "encryption modules are not built\n");
}
