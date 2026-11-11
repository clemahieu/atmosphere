// SPDX-License-Identifier: MIT

/* Host shim for the reference mdb.c.
 *
 * Service fds stand in for the data file, the O_DSYNC meta fd, and the lock
 * fd. The data map is a private mirror of the service: the service is not a
 * POSIX file, and mdb.c reads pages through the map. The lock map is a real
 * MAP_SHARED memfd so the process-shared pthread mutex in mdb_env_setup_locks
 * runs on shared memory. Record locks go to the service. Robust mutexes are
 * not emulated; mdb.c is built with MDB_USE_ROBUST=0.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <unistd.h>
#include <limits.h>

#include "lmdb.h"

struct atmo_ops {
	int64_t (*pread)(uint64_t offset, void *buf, size_t len);
	int64_t (*pwrite)(uint64_t offset, const void *buf, size_t len);
	int64_t (*sync_pwrite)(uint64_t offset, const void *buf, size_t len);
	int (*fdatasync)(void);
	int (*set_map_size)(uint64_t size);
	int (*lock_exclusive)(uint64_t offset);
	int (*lock_shared)(uint64_t offset);
	int (*lock_blocks)(uint64_t offset);
	uint64_t (*size)(void);
};

static struct atmo_ops ops;

void atmo_fs_bind(const struct atmo_ops *src)
{
	ops = *src;
}

enum { FD_BASE = 1000000, NFD = 3, SLOT_DATA = 0, SLOT_META = 1, SLOT_LOCK = 2 };

static int live[NFD];
static off_t pos[NFD];
static off_t lock_len;
static void *data_map;
static size_t data_map_len;
static void *lock_map;
static size_t lock_map_len;

int __real_open(const char *path, int flags, ...);
int __real_close(int fd);
ssize_t __real_pread(int fd, void *buf, size_t len, off_t offset);
ssize_t __real_pwrite(int fd, const void *buf, size_t len, off_t offset);
ssize_t __real_pwritev(int fd, const struct iovec *iov, int iovcnt, off_t offset);
ssize_t __real_read(int fd, void *buf, size_t len);
ssize_t __real_write(int fd, const void *buf, size_t len);
int __real_fstat(int fd, struct stat *st);
off_t __real_lseek(int fd, off_t off, int whence);
void *__real_mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
int __real_munmap(void *addr, size_t length);
int __real_ftruncate(int fd, off_t length);
int __real_fdatasync(int fd);
int __real_fcntl(int fd, int cmd, ...);
int __real_fsync(int fd);

static int our_slot(int fd)
{
	if (fd < FD_BASE || fd >= FD_BASE + NFD)
		return -1;
	return fd - FD_BASE;
}

static int live_slot(int fd)
{
	int slot = our_slot(fd);
	if (slot < 0 || !live[slot])
		return -1;
	return slot;
}

static int ready(void)
{
	if (!ops.pread || !ops.pwrite || !ops.sync_pwrite || !ops.fdatasync || !ops.size ||
	    !ops.lock_exclusive || !ops.lock_shared || !ops.lock_blocks) {
		errno = EIO;
		return -1;
	}
	return 0;
}

static void mirror_write(uint64_t offset, const void *buf, size_t len)
{
	size_t at;

	if (!data_map || len == 0 || offset >= data_map_len)
		return;
	at = (size_t)offset;
	if (len > data_map_len - at)
		len = data_map_len - at;
	memcpy((char *)data_map + at, buf, len);
}

static ssize_t write_bytes(int slot, off_t offset, const void *buf, size_t len, int update_pos)
{
	int64_t n;

	if (len == 0)
		return 0;
	if (offset < 0) {
		errno = EINVAL;
		return -1;
	}
	if (ready())
		return -1;
	if (slot == SLOT_LOCK) {
		if (!lock_map || (uint64_t)offset + len > lock_map_len) {
			errno = EIO;
			return -1;
		}
		memcpy((char *)lock_map + offset, buf, len);
		if (update_pos)
			pos[slot] = offset + (off_t)len;
		return (ssize_t)len;
	}
	n = (slot == SLOT_META) ? ops.sync_pwrite((uint64_t)offset, buf, len)
				: ops.pwrite((uint64_t)offset, buf, len);
	if (n < 0) {
		errno = EIO;
		return -1;
	}
	mirror_write((uint64_t)offset, buf, (size_t)n);
	if (update_pos)
		pos[slot] = offset + (off_t)n;
	return (ssize_t)n;
}

static ssize_t read_bytes(int slot, off_t offset, void *buf, size_t len, int update_pos)
{
	int64_t n;

	if (len == 0)
		return 0;
	if (offset < 0) {
		errno = EINVAL;
		return -1;
	}
	if (ready())
		return -1;
	if (slot == SLOT_LOCK) {
		size_t take;
		if (!lock_map || (uint64_t)offset >= lock_map_len)
			return 0;
		take = len;
		if ((uint64_t)offset + take > lock_map_len)
			take = lock_map_len - (size_t)offset;
		memcpy(buf, (char *)lock_map + offset, take);
		if (update_pos)
			pos[slot] = offset + (off_t)take;
		return (ssize_t)take;
	}
	n = ops.pread((uint64_t)offset, buf, len);
	if (n < 0) {
		errno = EIO;
		return -1;
	}
	if (update_pos)
		pos[slot] = offset + (off_t)n;
	return (ssize_t)n;
}

static int open_service(const char *path, int flags)
{
	const char *want;
	char lock[PATH_MAX];
	int slot;

	want = getenv("ATMO_LMDB_PATH");
	if (!want || !want[0])
		return -1;
	snprintf(lock, sizeof lock, "%s-lock", want);
	if (strcmp(path, lock) == 0)
		slot = SLOT_LOCK;
	else if (strcmp(path, want) == 0)
		slot = ((flags & O_ACCMODE) == O_WRONLY) ? SLOT_META : SLOT_DATA;
	else
		return -1;
	live[slot] = 1;
	pos[slot] = 0;
	if (slot == SLOT_LOCK)
		lock_len = 0;
	return FD_BASE + slot;
}

int __wrap_open(const char *path, int flags, ...)
{
	int mode;
	int fd;
	va_list ap;

	va_start(ap, flags);
	mode = va_arg(ap, int);
	va_end(ap);
	if (!path) {
		errno = EFAULT;
		return -1;
	}
	fd = open_service(path, flags);
	if (fd >= 0)
		return fd;
	return __real_open(path, flags, mode);
}

int __wrap_close(int fd)
{
	int slot = our_slot(fd);

	if (slot >= 0) {
		if (!live[slot]) {
			errno = EBADF;
			return -1;
		}
		/* One client serves every fd. Closing the meta fd is not the holder's death. */
		live[slot] = 0;
		pos[slot] = 0;
		return 0;
	}
	return __real_close(fd);
}

ssize_t __wrap_pread(int fd, void *buf, size_t len, off_t offset)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_pread(fd, buf, len, offset);
	}
	return read_bytes(slot, offset, buf, len, 0);
}

ssize_t __wrap_pwrite(int fd, const void *buf, size_t len, off_t offset)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_pwrite(fd, buf, len, offset);
	}
	return write_bytes(slot, offset, buf, len, 0);
}

ssize_t __wrap_pwritev(int fd, const struct iovec *iov, int iovcnt, off_t offset)
{
	int slot = live_slot(fd);
	ssize_t total = 0;
	int i;

	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_pwritev(fd, iov, iovcnt, offset);
	}
	if (iovcnt < 0) {
		errno = EINVAL;
		return -1;
	}
	for (i = 0; i < iovcnt; i++) {
		ssize_t n = write_bytes(slot, offset, iov[i].iov_base, iov[i].iov_len, 0);
		if (n < 0)
			return -1;
		if ((size_t)n != iov[i].iov_len) {
			errno = EIO;
			return -1;
		}
		offset += n;
		total += n;
	}
	return total;
}

ssize_t __wrap_read(int fd, void *buf, size_t len)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_read(fd, buf, len);
	}
	return read_bytes(slot, pos[slot], buf, len, 1);
}

ssize_t __wrap_write(int fd, const void *buf, size_t len)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_write(fd, buf, len);
	}
	return write_bytes(slot, pos[slot], buf, len, 1);
}

int __wrap_fstat(int fd, struct stat *st)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_fstat(fd, st);
	}
	if (!st || ready()) {
		errno = st ? EIO : EFAULT;
		return -1;
	}
	memset(st, 0, sizeof *st);
	st->st_mode = S_IFREG | 0644;
	st->st_nlink = 1;
	st->st_blksize = 4096;
	st->st_size = (slot == SLOT_LOCK) ? lock_len : (off_t)ops.size();
	return 0;
}

off_t __wrap_lseek(int fd, off_t off, int whence)
{
	int slot = live_slot(fd);
	off_t end, next;

	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_lseek(fd, off, whence);
	}
	if (ready())
		return -1;
	end = (slot == SLOT_LOCK) ? lock_len : (off_t)ops.size();
	if (whence == SEEK_SET)
		next = off;
	else if (whence == SEEK_CUR)
		next = pos[slot] + off;
	else if (whence == SEEK_END)
		next = end + off;
	else {
		errno = EINVAL;
		return -1;
	}
	if (next < 0) {
		errno = EINVAL;
		return -1;
	}
	pos[slot] = next;
	return next;
}

static void *map_data(size_t length)
{
	void *p;
	uint64_t off = 0;

	if (data_map) {
		__real_munmap(data_map, data_map_len);
		data_map = NULL;
		data_map_len = 0;
	}
	p = __real_mmap(NULL, length, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	if (p == MAP_FAILED)
		return MAP_FAILED;
	while (off < length) {
		size_t chunk = length - (size_t)off;
		int64_t n;
		if (chunk > 1024 * 1024)
			chunk = 1024 * 1024;
		n = ops.pread(off, (char *)p + off, chunk);
		if (n < 0) {
			__real_munmap(p, length);
			errno = EIO;
			return MAP_FAILED;
		}
		if (n == 0)
			break;
		off += (uint64_t)n;
	}
	data_map = p;
	data_map_len = length;
	return p;
}

static void *map_lock(size_t length)
{
	int mfd;
	void *p;

	if (lock_map) {
		__real_munmap(lock_map, lock_map_len);
		lock_map = NULL;
		lock_map_len = 0;
	}
	mfd = memfd_create("atmo-lmdb-lock", 0);
	if (mfd < 0)
		return MAP_FAILED;
	if (__real_ftruncate(mfd, (off_t)length) != 0) {
		__real_close(mfd);
		return MAP_FAILED;
	}
	p = __real_mmap(NULL, length, PROT_READ | PROT_WRITE, MAP_SHARED, mfd, 0);
	__real_close(mfd);
	if (p == MAP_FAILED)
		return MAP_FAILED;
	lock_map = p;
	lock_map_len = length;
	lock_len = (off_t)length;
	return p;
}

void *__wrap_mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset)
{
	int slot = live_slot(fd);
	(void)addr;
	(void)prot;
	(void)flags;
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return MAP_FAILED;
		}
		return __real_mmap(addr, length, prot, flags, fd, offset);
	}
	if (length == 0 || offset != 0 || ready()) {
		errno = ready() ? errno : EINVAL;
		return MAP_FAILED;
	}
	if (slot == SLOT_LOCK)
		return map_lock(length);
	return map_data(length);
}

int __wrap_munmap(void *addr, size_t length)
{
	if (addr && addr == data_map) {
		data_map = NULL;
		data_map_len = 0;
	} else if (addr && addr == lock_map) {
		lock_map = NULL;
		lock_map_len = 0;
	}
	return __real_munmap(addr, length);
}

int __wrap_ftruncate(int fd, off_t length)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_ftruncate(fd, length);
	}
	if (length < 0 || ready()) {
		if (length < 0)
			errno = EINVAL;
		return -1;
	}
	if (slot == SLOT_LOCK) {
		lock_len = length;
		return 0;
	}
	if (ops.set_map_size((uint64_t)length) != 0) {
		errno = EIO;
		return -1;
	}
	return 0;
}

static int sync_fd(int fd)
{
	int slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return -2;
	}
	if (slot == SLOT_LOCK)
		return 0;
	if (ready() || ops.fdatasync() != 0) {
		errno = EIO;
		return -1;
	}
	return 0;
}

int __wrap_fdatasync(int fd)
{
	int rc = sync_fd(fd);
	if (rc == -2)
		return __real_fdatasync(fd);
	return rc;
}

int __wrap_fsync(int fd)
{
	int rc = sync_fd(fd);
	if (rc == -2)
		return __real_fsync(fd);
	return rc;
}

static int lock_fcntl(int cmd, struct flock *lk)
{
	uint64_t off;
	int rc;

	if (!lk || lk->l_len != 1 || lk->l_whence != SEEK_SET || lk->l_start < 0) {
		errno = EINVAL;
		return -1;
	}
	if (ready())
		return -1;
	off = (uint64_t)lk->l_start;
	if (cmd == F_GETLK) {
		int blocked = ops.lock_blocks(off);
		if (blocked < 0) {
			errno = EIO;
			return -1;
		}
		if (blocked) {
			lk->l_type = F_WRLCK;
			lk->l_pid = (getpid() == 1) ? 2 : 1;
		} else {
			lk->l_type = F_UNLCK;
		}
		return 0;
	}
	if (lk->l_type == F_WRLCK)
		rc = ops.lock_exclusive(off);
	else if (lk->l_type == F_RDLCK)
		rc = ops.lock_shared(off);
	else if (lk->l_type == F_UNLCK)
		rc = 0;
	else {
		errno = EINVAL;
		return -1;
	}
	if (rc == -2) {
		errno = EAGAIN;
		return -1;
	}
	if (rc != 0) {
		errno = EIO;
		return -1;
	}
	return 0;
}

int __wrap_fcntl(int fd, int cmd, ...)
{
	long arg;
	int slot;
	va_list ap;

	va_start(ap, cmd);
	arg = va_arg(ap, long);
	va_end(ap);
	slot = live_slot(fd);
	if (slot < 0) {
		if (our_slot(fd) >= 0) {
			errno = EBADF;
			return -1;
		}
		return __real_fcntl(fd, cmd, arg);
	}
	if (cmd == F_GETFD)
		return FD_CLOEXEC;
	if (cmd == F_SETFD || cmd == F_SETFL || cmd == F_GETFL)
		return (cmd == F_GETFL) ? 0 : 0;
	if (slot == SLOT_LOCK && (cmd == F_SETLK || cmd == F_SETLKW || cmd == F_GETLK))
		return lock_fcntl(cmd, (struct flock *)arg);
	errno = EINVAL;
	return -1;
}

static int fail(const char *step, int rc, MDB_txn *txn, MDB_env *env)
{
	fprintf(stderr, "lmdb %s: %s\n", step, mdb_strerror(rc));
	if (txn)
		mdb_txn_abort(txn);
	if (env)
		mdb_env_close(env);
	return rc;
}

static const char *db_path(void)
{
	const char *path = getenv("ATMO_LMDB_PATH");
	if (!path || !path[0]) {
		fprintf(stderr, "lmdb path: ATMO_LMDB_PATH is unset\n");
		return NULL;
	}
	return path;
}

static int open_env(uint64_t mapsize, MDB_env **env)
{
	const char *path = db_path();
	int rc;
	if (!path)
		return ENOENT;
	rc = mdb_env_create(env);
	if (rc)
		return fail("create", rc, NULL, NULL);
	rc = mdb_env_set_mapsize(*env, (mdb_size_t)mapsize);
	if (rc)
		return fail("set_mapsize", rc, NULL, *env);
	rc = mdb_env_open(*env, path, MDB_NOSUBDIR | MDB_NOTLS | MDB_NORDAHEAD, 0644);
	if (rc)
		return fail("open", rc, NULL, *env);
	return 0;
}

int atmo_lmdb_put(uint64_t mapsize, const void *key, size_t key_len, const void *val, size_t val_len)
{
	MDB_env *env = NULL;
	MDB_txn *txn = NULL;
	MDB_dbi dbi;
	MDB_val k, v;
	int rc = open_env(mapsize, &env);
	if (rc)
		return rc;
	rc = mdb_txn_begin(env, NULL, 0, &txn);
	if (rc)
		return fail("begin", rc, NULL, env);
	rc = mdb_dbi_open(txn, NULL, 0, &dbi);
	if (rc)
		return fail("dbi", rc, txn, env);
	k.mv_data = (void *)key;
	k.mv_size = key_len;
	v.mv_data = (void *)val;
	v.mv_size = val_len;
	rc = mdb_put(txn, dbi, &k, &v, 0);
	if (rc)
		return fail("put", rc, txn, env);
	rc = mdb_txn_commit(txn);
	if (rc)
		return fail("commit", rc, NULL, env);
	mdb_env_close(env);
	return 0;
}

int atmo_lmdb_get(uint64_t mapsize, const void *key, size_t key_len,
		void *val, size_t val_cap, size_t *val_len)
{
	MDB_env *env = NULL;
	MDB_txn *txn = NULL;
	MDB_dbi dbi;
	MDB_val k, v;
	int rc = open_env(mapsize, &env);
	if (rc)
		return rc;
	rc = mdb_txn_begin(env, NULL, MDB_RDONLY, &txn);
	if (rc)
		return fail("begin", rc, NULL, env);
	rc = mdb_dbi_open(txn, NULL, 0, &dbi);
	if (rc)
		return fail("dbi", rc, txn, env);
	k.mv_data = (void *)key;
	k.mv_size = key_len;
	rc = mdb_get(txn, dbi, &k, &v);
	if (rc)
		return fail("get", rc, txn, env);
	if (v.mv_size > val_cap) {
		return fail("get", EINVAL, txn, env);
	}
	memcpy(val, v.mv_data, v.mv_size);
	if (val_len)
		*val_len = v.mv_size;
	mdb_txn_abort(txn);
	mdb_env_close(env);
	return 0;
}
