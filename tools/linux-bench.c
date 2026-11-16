// SPDX-License-Identifier: MIT
// The Linux half of the mapped microbenchmarks. One static binary, no C library and no
// kernel header: every call is the x86_64 syscall ABI. tools/linux-bench.py links this
// into an initramfs and boots the host kernel. The labels are Atmosphere's; what each
// operation includes is the Linux guest section of design/synthetic-benchmark-suite/.

typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;
typedef long int64_t;

enum { BATCHES = 20, ITERS = 16, WARMUP = 4, FAULT_PAGES = 1024, STACK_BYTES = 16384 };

enum {
    CLONE_VM = 0x00000100,
    CLONE_FS = 0x00000200,
    CLONE_FILES = 0x00000400,
    CLONE_SIGHAND = 0x00000800,
    CLONE_THREAD = 0x00010000,
    CLONE_PARENT_SETTID = 0x00100000,
    CLONE_CHILD_CLEARTID = 0x00200000,
};

enum { FUTEX_WAIT = 0, FUTEX_WAKE = 1, FUTEX_PRIVATE = 128 };

enum { SYS_READ = 0, SYS_WRITE = 1, SYS_OPEN = 2, SYS_CLOSE = 3, SYS_MMAP = 9, SYS_MUNMAP = 11 };
enum { SYS_IOCTL = 16, SYS_NANOSLEEP = 35, SYS_FORK = 57, SYS_EXECVE = 59, SYS_EXIT = 60 };
enum { SYS_WAIT4 = 61, SYS_GETPPID = 110, SYS_MOUNT = 165, SYS_REBOOT = 169 };
enum { SYS_FUTEX = 202, SYS_SCHED_SETAFFINITY = 203, SYS_EXIT_GROUP = 231, SYS_PERF_EVENT_OPEN = 298 };
enum { SYS_CLONE = 56 };

enum { PROT_RW = 3, MAP_ANON_PRIVATE = 0x22 };
enum { O_WRONLY = 1 };
enum { PERF_IOC_ENABLE = 0x2400, PERF_IOC_DISABLE = 0x2401, PERF_IOC_RESET = 0x2403 };

static const unsigned long CLONE_JOIN =
    CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD | CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID;

static char spawn_path[] = "/init";
static char spawn_arg1[] = "child";
static char *spawn_argv[] = {spawn_path, spawn_arg1, 0};
static char *spawn_envp[1] = {0};

static volatile long sink;
static int child_tid;
static int turn;
static int stop;
static int peer_cpu;
static void (*child_entry)(void);
static void *peer_stack;
static void *thread_stack;
static int counters_mode;
static int pmu_fd[3];

static uint32_t atom32;
static uint64_t atom64;
static uint64_t cell;
static int lockword;
static int futex_word;
static uint8_t copy_src[100000];
static uint8_t copy_dst[100000];

static char json_buf[1 << 16];
static int json_len;
static int json_first = 1;

static long sc0(long n) {
    long ret;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n) : "rcx", "r11", "memory");
    return ret;
}

static long sc1(long n, long a) {
    long ret;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n), "D"(a) : "rcx", "r11", "memory");
    return ret;
}

static long sc2(long n, long a, long b) {
    long ret;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n), "D"(a), "S"(b) : "rcx", "r11", "memory");
    return ret;
}

static long sc3(long n, long a, long b, long c) {
    long ret;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory");
    return ret;
}

static long sc4(long n, long a, long b, long c, long d) {
    long ret;
    register long r10 __asm__("r10") = d;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10) : "rcx", "r11", "memory");
    return ret;
}

static long sc5(long n, long a, long b, long c, long d, long e) {
    long ret;
    register long r10 __asm__("r10") = d;
    register long r8 __asm__("r8") = e;
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8)
                     : "rcx", "r11", "memory");
    return ret;
}

static long sc6(long n, long a, long b, long c, long d, long e, long f) {
    long ret;
    register long r10 __asm__("r10") = d;
    register long r8 __asm__("r8") = e;
    register long r9 __asm__("r9") = f;
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8), "r"(r9)
                     : "rcx", "r11", "memory");
    return ret;
}

static void wr(const char *s) {
    uint64_t n = 0;
    while (s[n]) n++;
    sc3(SYS_WRITE, 1, (long)s, (long)n);
}

static void wr_dec(long v) {
    char rev[24];
    int n = 0;
    uint64_t u;
    if (v < 0) {
        wr("-");
        u = (uint64_t)(-v);
    } else {
        u = (uint64_t)v;
    }
    if (u == 0) rev[n++] = '0';
    while (u) {
        rev[n++] = (char)('0' + (u % 10));
        u /= 10;
    }
    while (n) {
        char one[2] = {rev[--n], 0};
        wr(one);
    }
}

static void reboot_off(void) { sc4(SYS_REBOOT, 0xfee1dead, 0x28121969, 0x4321fedc, 0); }

__attribute__((noreturn)) static void die_errno(const char *msg, long err) {
    wr("linux-bench fail: ");
    wr(msg);
    wr(" ");
    wr_dec(err);
    wr("\n");
    reboot_off();
    for (;;) sc1(SYS_EXIT_GROUP, 1);
}

__attribute__((noreturn)) static void die(const char *msg) { die_errno(msg, 0); }

static int same(const char *a, const char *b) {
    while (*a && *a == *b) {
        a++;
        b++;
    }
    return *a == *b;
}

static int contains(const char *hay, const char *needle) {
    for (int i = 0; hay[i]; i++) {
        int j = 0;
        while (needle[j] && hay[i + j] == needle[j]) j++;
        if (!needle[j]) return 1;
    }
    return 0;
}

static void pin(int cpu) {
    unsigned long mask = 1UL << cpu;
    long r = sc3(SYS_SCHED_SETAFFINITY, 0, 8, (long)&mask);
    if (r < 0) die_errno("affinity", r);
}

static void pause_ms(int ms) {
    long ts[2] = {0, (long)ms * 1000000L};
    sc2(SYS_NANOSLEEP, (long)ts, 0);
}

static inline uint64_t ticks(void) {
    uint32_t lo, hi;
    __asm__ volatile("lfence; rdtsc; lfence" : "=a"(lo), "=d"(hi)::"memory");
    return ((uint64_t)hi << 32) | lo;
}

static long futex(int *addr, long op, int val, long timeout) {
    return sc4(SYS_FUTEX, (long)addr, op, (long)val, timeout);
}

static void futex_wake(int *addr) { futex(addr, FUTEX_WAKE | FUTEX_PRIVATE, 1, 0); }

// A lost wake (the kernel's clear_child_tid uses the shared queue) retries on the timeout.
static void fwait(int *addr, int val) {
    long ts[2] = {0, 2000000L};
    while (__atomic_load_n(addr, __ATOMIC_ACQUIRE) == val) futex(addr, FUTEX_WAIT | FUTEX_PRIVATE, val, (long)ts);
}

__attribute__((used, noinline, noclone)) static void thread_child(void) { child_entry(); }

// The kernel returns the child at the instruction after syscall, with rsp set to `stack`.
// The child must not fall back into this frame, so it exits inside the asm.
static long clone_thread(void *stack) {
    long ret;
    register long r10 __asm__("r10") = (long)&child_tid;
    register long r8 __asm__("r8") = 0;
    __asm__ volatile("syscall\n\t"
                     "test %%rax, %%rax\n\t"
                     "jnz 1f\n\t"
                     "call thread_child\n\t"
                     "mov $60, %%rax\n\t"
                     "xor %%rdi, %%rdi\n\t"
                     "syscall\n\t"
                     "1:\n\t"
                     : "=a"(ret)
                     : "a"((long)SYS_CLONE), "D"(CLONE_JOIN), "S"(stack), "d"(&child_tid), "r"(r10), "r"(r8)
                     : "rcx", "r11", "memory");
    return ret;
}

static void join_child(void) {
    long ts[2] = {0, 2000000L};
    for (int spins = 0; __atomic_load_n(&child_tid, __ATOMIC_ACQUIRE) != 0; spins++) {
        if (spins > 100000) die("join");
        futex(&child_tid, FUTEX_WAIT, child_tid, (long)ts);
    }
}

static void *map_stack(void) {
    long p = sc6(SYS_MMAP, 0, STACK_BYTES, PROT_RW, MAP_ANON_PRIVATE, -1, 0);
    if (p < 0) die_errno("stack", p);
    ((uint8_t *)p)[STACK_BYTES - 1] = 0;
    return (void *)(p + STACK_BYTES);
}

static void start_peer(void (*fn)(void), int cpu) {
    peer_cpu = cpu;
    child_entry = fn;
    __atomic_store_n(&stop, 0, __ATOMIC_RELAXED);
    __atomic_store_n(&turn, 0, __ATOMIC_RELAXED);
    child_tid = 0;
    long r = clone_thread(peer_stack);
    if (r < 0) die_errno("peer", r);
}

static void stop_peer(void) {
    __atomic_store_n(&stop, 1, __ATOMIC_RELEASE);
    __atomic_store_n(&turn, 1, __ATOMIC_RELEASE);
    futex_wake(&turn);
    join_child();
}

static void peer_futex(void) {
    pin(peer_cpu);
    for (;;) {
        fwait(&turn, 0);
        if (__atomic_load_n(&stop, __ATOMIC_ACQUIRE)) return;
        __atomic_store_n(&turn, 0, __ATOMIC_RELEASE);
        futex_wake(&turn);
    }
}

static void peer_atomic(void) {
    pin(1);
    while (!__atomic_load_n(&stop, __ATOMIC_ACQUIRE)) __atomic_fetch_add(&cell, 1, __ATOMIC_RELAXED);
}

static void child_return(void) {}

static void jadd(const char *s) {
    while (*s) {
        if (json_len >= (int)sizeof json_buf - 1) die("json overflow");
        json_buf[json_len++] = *s++;
    }
}

static void jdec(uint64_t whole, uint32_t frac) {
    char rev[24];
    char tmp[40];
    int n = 0;
    int r = 0;
    uint64_t w = whole;
    if (w == 0) rev[r++] = '0';
    while (w) {
        rev[r++] = (char)('0' + (w % 10));
        w /= 10;
    }
    while (r) tmp[n++] = rev[--r];
    tmp[n++] = '.';
    tmp[n++] = (char)('0' + (frac / 1000) % 10);
    tmp[n++] = (char)('0' + (frac / 100) % 10);
    tmp[n++] = (char)('0' + (frac / 10) % 10);
    tmp[n++] = (char)('0' + frac % 10);
    tmp[n] = 0;
    jadd(tmp);
}

static void split_by(uint64_t delta, uint64_t divisor, uint64_t *whole, uint32_t *frac) {
    *whole = delta / divisor;
    *frac = (uint32_t)((delta % divisor) * 10000 / divisor);
}

static void emit(const char *label, const char *suffix, const char *unit, const uint64_t *whole, const uint32_t *frac) {
    if (!json_first) jadd(",\n");
    json_first = 0;
    jadd("{\"label\":\"");
    jadd(label);
    jadd(suffix);
    jadd("\",\"test_suite\":\"linux.microbenchmarks\",\"unit\":\"");
    jadd(unit);
    jadd("\",\"values\":[");
    for (int b = 0; b < BATCHES; b++) {
        if (b) jadd(",");
        jdec(whole[b], frac[b]);
    }
    jadd("]}");
}

static void wr32(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

static void wr64(uint8_t *p, uint64_t v) {
    wr32(p, (uint32_t)v);
    wr32(p + 4, (uint32_t)(v >> 32));
}

static long pmu_open(uint32_t type, uint64_t config) {
    uint8_t attr[64];
    for (int i = 0; i < 64; i++) attr[i] = 0;
    wr32(attr, type);
    wr32(attr + 4, 64);
    wr64(attr + 8, config);
    // disabled until the batch starts; exclude the hypervisor, count user and kernel.
    wr64(attr + 40, (1ULL << 0) | (1ULL << 7));
    return sc5(SYS_PERF_EVENT_OPEN, (long)attr, 0, -1, -1, 0);
}

static void pmu_ioctl(int cmd) {
    for (int i = 0; i < 3; i++) {
        long r = sc3(SYS_IOCTL, pmu_fd[i], cmd, 0);
        if (r < 0) die_errno("pmu ioctl", r);
    }
}

static uint64_t pmu_read(int fd) {
    uint64_t v = 0;
    long n = sc3(SYS_READ, fd, (long)&v, 8);
    if (n != 8) die_errno("pmu read", n);
    return v;
}

static void pmu_setup(void) {
    long fd = sc3(SYS_OPEN, (long)"/proc/sys/kernel/perf_event_paranoid", O_WRONLY, 0);
    if (fd >= 0) {
        sc3(SYS_WRITE, fd, (long)"-1", 2);
        sc1(SYS_CLOSE, fd);
    }
    long cyc = pmu_open(0, 0);
    if (cyc < 0) cyc = pmu_open(4, 0x76);
    if (cyc < 0) die_errno("cycles", cyc);
    long ins = pmu_open(0, 1);
    if (ins < 0) ins = pmu_open(4, 0xc0);
    if (ins < 0) die_errno("instructions", ins);
    long fills = pmu_open(4, 0x5f44);
    if (fills < 0) die_errno("fills", fills);
    pmu_fd[0] = (int)cyc;
    pmu_fd[1] = (int)ins;
    pmu_fd[2] = (int)fills;
    wr("linux-bench pmu open\n");
}

static void pmu_begin(void) {
    pmu_ioctl(PERF_IOC_RESET);
    pmu_ioctl(PERF_IOC_ENABLE);
}

static void pmu_end(uint64_t *cyc, uint64_t *ins, uint64_t *fills) {
    pmu_ioctl(PERF_IOC_DISABLE);
    *cyc = pmu_read(pmu_fd[0]);
    *ins = pmu_read(pmu_fd[1]);
    *fills = pmu_read(pmu_fd[2]);
}

typedef void (*op_fn)(void *);

static void run_one(const char *label, op_fn op, void *arg) {
    uint64_t tw[BATCHES], tc[BATCHES], ti[BATCHES], tf[BATCHES];
    uint32_t fw[BATCHES], fc[BATCHES], fi[BATCHES], ff[BATCHES];
    wr("linux-bench run ");
    wr(label);
    wr("\n");
    for (int i = 0; i < WARMUP; i++) op(arg);
    for (int b = 0; b < BATCHES; b++) {
        if (counters_mode) pmu_begin();
        uint64_t t0 = ticks();
        for (int i = 0; i < ITERS; i++) op(arg);
        uint64_t t1 = ticks();
        uint64_t cyc = 0, ins = 0, fills = 0;
        if (counters_mode) pmu_end(&cyc, &ins, &fills);
        split_by(t1 - t0, ITERS, &tw[b], &fw[b]);
        if (counters_mode) {
            split_by(cyc, ITERS, &tc[b], &fc[b]);
            split_by(ins, ITERS, &ti[b], &fi[b]);
            split_by(fills, ITERS, &tf[b], &ff[b]);
        }
    }
    if (counters_mode) {
        emit(label, ".cycles", "cycles", tc, fc);
        emit(label, ".instructions", "instructions", ti, fi);
        emit(label, ".fills", "count", tf, ff);
    } else {
        emit(label, ".tsc_cycles", "cycles", tw, fw);
    }
}

static void op_null(void *a) { (void)a; }

static void op_loop(void *a) {
    unsigned long n = (unsigned long)a;
    for (unsigned long i = 0; i < n; i++) __asm__ volatile("" ::: "memory");
}

static void op_getppid(void *a) {
    (void)a;
    sink = sc0(SYS_GETPPID);
}

static void op_wake(void *a) {
    (void)a;
    futex(&futex_word, FUTEX_WAKE | FUTEX_PRIVATE, 1, 0);
}

static void op_futex_rt(void *a) {
    (void)a;
    __atomic_store_n(&turn, 1, __ATOMIC_RELEASE);
    futex_wake(&turn);
    fwait(&turn, 1);
}

static void handoff(const char *label, int cpu) {
    start_peer(peer_futex, cpu);
    pause_ms(20);
    run_one(label, op_futex_rt, 0);
    stop_peer();
}

static void op_thread(void *a) {
    (void)a;
    child_entry = child_return;
    child_tid = 0;
    long r = clone_thread(thread_stack);
    if (r < 0) die_errno("clone", r);
    join_child();
}

static void op_spawn(void *a) {
    (void)a;
    long r = sc0(SYS_FORK);
    if (r < 0) die_errno("fork", r);
    if (r == 0) {
        sc3(SYS_EXECVE, (long)spawn_path, (long)spawn_argv, (long)spawn_envp);
        sc1(SYS_EXIT, 127);
        for (;;) {
        }
    }
    long status = 0;
    long w;
    do {
        w = sc4(SYS_WAIT4, r, (long)&status, 0, 0);
    } while (w == -4);
    if (w < 0 || (status & 0x7f) != 0 || ((status >> 8) & 0xff) != 0) die_errno("wait", w < 0 ? w : status);
}

static void op_map(void *a) {
    (void)a;
    long p = sc6(SYS_MMAP, 0, 4096, PROT_RW, MAP_ANON_PRIVATE, -1, 0);
    if (p < 0) die_errno("mmap", p);
    long u = sc2(SYS_MUNMAP, p, 4096);
    if (u < 0) die_errno("munmap", u);
}

static void op_add32(void *a) {
    (void)a;
    __atomic_fetch_add(&atom32, 1, __ATOMIC_RELAXED);
}
static void op_add64(void *a) {
    (void)a;
    __atomic_fetch_add(&atom64, 1, __ATOMIC_RELAXED);
}
static void op_cmp32(void *a) {
    (void)a;
    uint32_t expected = __atomic_load_n(&atom32, __ATOMIC_RELAXED);
    __atomic_compare_exchange_n(&atom32, &expected, expected + 1, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED);
}
static void op_cmp64(void *a) {
    (void)a;
    uint64_t expected = __atomic_load_n(&atom64, __ATOMIC_RELAXED);
    __atomic_compare_exchange_n(&atom64, &expected, expected + 1, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED);
}
static void op_cmp_far(void *a) {
    (void)a;
    uint64_t expected = __atomic_load_n(&cell, __ATOMIC_RELAXED);
    __atomic_compare_exchange_n(&cell, &expected, expected + 1, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED);
}
static void op_mutex(void *a) {
    (void)a;
    while (__atomic_exchange_n(&lockword, 1, __ATOMIC_ACQUIRE) != 0) {
    }
    __atomic_store_n(&lockword, 0, __ATOMIC_RELEASE);
}
static void op_copy(void *a) {
    uint64_t n = (uint64_t)(unsigned long)a;
    uint8_t *dst = copy_dst;
    uint8_t *src = copy_src;
    __asm__ volatile("rep movsb" : "+D"(dst), "+S"(src), "+c"(n)::"memory");
}
static void op_ticks(void *a) {
    (void)a;
    sink = (long)ticks();
}

static void fault_sweep(void) {
    uint64_t tw[BATCHES], tc[BATCHES], ti[BATCHES], tf[BATCHES];
    uint32_t fw[BATCHES], fc[BATCHES], fi[BATCHES], ff[BATCHES];
    wr("linux-bench run UserPager/PageFault/Sequential\n");
    for (int b = -1; b < BATCHES; b++) {
        long bytes = (long)FAULT_PAGES * 4096;
        long p = sc6(SYS_MMAP, 0, bytes, PROT_RW, MAP_ANON_PRIVATE, -1, 0);
        if (p < 0) die_errno("fault mmap", p);
        if (counters_mode && b >= 0) pmu_begin();
        uint64_t t0 = ticks();
        volatile uint8_t *page = (volatile uint8_t *)p;
        for (int i = 0; i < FAULT_PAGES; i++) page[(uint64_t)i * 4096] = 1;
        uint64_t t1 = ticks();
        uint64_t cyc = 0, ins = 0, fills = 0;
        if (counters_mode && b >= 0) pmu_end(&cyc, &ins, &fills);
        long u = sc2(SYS_MUNMAP, p, bytes);
        if (u < 0) die_errno("fault munmap", u);
        if (b >= 0) {
            split_by(t1 - t0, FAULT_PAGES, &tw[b], &fw[b]);
            if (counters_mode) {
                split_by(cyc, FAULT_PAGES, &tc[b], &fc[b]);
                split_by(ins, FAULT_PAGES, &ti[b], &fi[b]);
                split_by(fills, FAULT_PAGES, &tf[b], &ff[b]);
            }
        }
    }
    if (counters_mode) {
        emit("UserPager/PageFault/Sequential", ".cycles", "cycles", tc, fc);
        emit("UserPager/PageFault/Sequential", ".instructions", "instructions", ti, fi);
        emit("UserPager/PageFault/Sequential", ".fills", "count", tf, ff);
    } else {
        emit("UserPager/PageFault/Sequential", ".tsc_cycles", "cycles", tw, fw);
    }
}

static void contended(void) {
    start_peer(peer_atomic, 1);
    pause_ms(20);
    run_one("Atomic/ContendedCmpxchg/DiffCore", op_cmp_far, 0);
    stop_peer();
}

static int read_all(const char *path, char *buf, int cap) {
    long fd = sc3(SYS_OPEN, (long)path, 0, 0);
    if (fd < 0) return -1;
    long n = sc3(SYS_READ, fd, (long)buf, cap - 1);
    sc1(SYS_CLOSE, fd);
    if (n < 0) return -1;
    buf[n] = 0;
    return (int)n;
}

static void mount_proc(void) {
    long r = sc5(SYS_MOUNT, (long)"proc", (long)"/proc", (long)"proc", 0, 0);
    if (r < 0) die_errno("mount", r);
}

int main(int argc, char **argv) {
    if (argc > 1 && same(argv[1], "child")) {
        sc1(SYS_EXIT_GROUP, 0);
        for (;;) {
        }
    }
    mount_proc();
    char cmdline[512];
    if (read_all("/proc/cmdline", cmdline, (int)sizeof cmdline) < 0) die("cmdline");
    counters_mode = contains(cmdline, "bench.counters=1");
    pin(0);
    if (counters_mode) pmu_setup();
    peer_stack = map_stack();
    thread_stack = map_stack();
    for (int i = 0; i < 100000; i++) copy_src[i] = (uint8_t)i;

    wr("linux-bench ready\n");
    run_one("Null", op_null, 0);
    run_one("NoOpLoop/100", op_loop, (void *)100UL);
    run_one("NoOpLoop/1000", op_loop, (void *)1000UL);
    run_one("NoOpLoop/10000", op_loop, (void *)10000UL);
    run_one("Syscall/Null", op_getppid, 0);
    run_one("Notification/Signal", op_wake, 0);
    handoff("Notification/RoundTrip_SameCore", 0);
    handoff("Notification/RoundTrip_DiffCore", 1);
    handoff("ContextSwitch/SameProcess", 0);
    run_one("Thread/CreateStartJoin", op_thread, 0);
    run_one("Process/SpawnWait", op_spawn, 0);
    run_one("Mmu/MapUnmap/4K", op_map, 0);
    fault_sweep();
    run_one("Atomic/Increment/32bit", op_add32, 0);
    run_one("Atomic/Increment/64bit", op_add64, 0);
    run_one("Atomic/Cmpxchg/32bit", op_cmp32, 0);
    run_one("Atomic/Cmpxchg/64bit", op_cmp64, 0);
    contended();
    run_one("Mutex/FastLockUnlock", op_mutex, 0);
    run_one("Memcpy/1000bytes", op_copy, (void *)1000UL);
    run_one("Memcpy/100000bytes", op_copy, (void *)100000UL);
    run_one("TicksGet", op_ticks, 0);

    wr("--- FUCHSIAPERF JSON BEGIN ---\n[");
    sc3(SYS_WRITE, 1, (long)json_buf, json_len);
    wr("]\n--- FUCHSIAPERF JSON END ---\n");
    reboot_off();
    for (;;) sc1(SYS_EXIT_GROUP, 0);
}

__asm__(".global _start\n"
        "_start:\n\t"
        "xor %ebp, %ebp\n\t"
        "mov (%rsp), %edi\n\t"
        "lea 8(%rsp), %rsi\n\t"
        "and $-16, %rsp\n\t"
        "call main\n\t"
        "mov %eax, %edi\n\t"
        "mov $231, %eax\n\t"
        "syscall\n");
