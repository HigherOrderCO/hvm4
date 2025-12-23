#include <sys/mman.h>

#ifndef MAP_NORESERVE
#define MAP_NORESERVE 0
#endif

fn void wnf_stack_init(void) {
  WnfBank *bank = WNF_BANK;
  if (bank->stack) {
    return;
  }

  u64 bytes = WNF_CAP * sizeof(Term);
  int prot  = PROT_READ | PROT_WRITE;
  int flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE;
  Term *stack = (Term *)mmap(NULL, bytes, prot, flags, -1, 0);
  u8 stack_mmap = 1;

  if (stack == MAP_FAILED) {
    stack = (Term *)malloc(bytes);
    stack_mmap = 0;
  }

  if (!stack) {
    fprintf(stderr, "wnf: stack allocation failed\n");
    exit(1);
  }

  bank->stack       = stack;
  bank->stack_bytes = bytes;
  bank->stack_mmap  = stack_mmap;
  bank->s_pos       = 1;
}
