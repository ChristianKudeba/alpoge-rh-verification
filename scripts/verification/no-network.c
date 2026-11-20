/* Extra process restriction for Comparator's documented AF_UNIX issue.
 * Linux x86-64 only. Refuse root, old Landlock, and non-native syscall ABIs;
 * deny creation of all sockets, including AF_UNIX, in this process and children.
 * This is additional to genuine Landrun, never a replacement for it.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <unistd.h>

#if !defined(__x86_64__)
#error "This reviewed launcher supports Linux x86-64 only"
#endif

static void fail(const char *message) { perror(message); exit(125); }

int main(int argc, char **argv) {
  if (argc < 2) { fputs("usage: no-network COMMAND [ARGS...]\n", stderr); return 125; }
  if (getuid() == 0 || geteuid() == 0) {
    fputs("Comparator must run as an unprivileged user\n", stderr); return 125;
  }
  long abi = syscall(SYS_landlock_create_ruleset, NULL, 0, 1);
  if (abi < 6) {
    fprintf(stderr, "Landlock ABI >= 6 required; observed %ld (errno %d)\n", abi, errno);
    return 125;
  }
  /* Avoid passing inherited communication descriptors to the checked process. */
  if (syscall(SYS_close_range, 3u, ~0u, 0u) != 0) fail("close_range");
  struct sock_filter filter[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
    BPF_JUMP(BPF_JMP | BPF_JSET | BPF_K, 0x40000000u, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_socket, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_socketpair, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
    /* io_uring can otherwise issue socket operations without SYS_socket. */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_io_uring_setup, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | EPERM),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
  };
  struct sock_fprog program = {
    .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])), .filter = filter
  };
  if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) fail("no_new_privs");
  if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program)) fail("seccomp");
  execvp(argv[1], argv + 1);
  fail("execvp");
}
