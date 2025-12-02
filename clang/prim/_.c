// Forward declare wnf
fn Term wnf(Term term);

// Primitive name constants
#define PRIM_ADD 4356
#define PRIM_SUB 79170
#define PRIM_MUL 54604
#define PRIM_DIV 16982
#define PRIM_MOD 54212
#define PRIM_AND 4996
#define PRIM_OR  978
#define PRIM_XOR 99282
#define PRIM_LSH 50376
#define PRIM_RSH 74952
#define PRIM_NOT 58324
#define PRIM_EQ  337
#define PRIM_NE  901
#define PRIM_LT  788
#define PRIM_LE  773
#define PRIM_GT  468
#define PRIM_GE  453
#define PRIM_DUP 17744
#define PRIM_SUP 79184

// Primitive implementations
#include "add.c"
#include "sub.c"
#include "mul.c"
#include "div.c"
#include "mod.c"
#include "and.c"
#include "or.c"
#include "xor.c"
#include "lsh.c"
#include "rsh.c"
#include "not.c"
#include "dup.c"
#include "sup.c"
#include "eq.c"
#include "ne.c"
#include "lt.c"
#include "le.c"
#include "gt.c"
#include "ge.c"

// Dispatch a primitive call
fn Term prim_call(u32 nam, u32 ari, u32 loc) {
  switch (nam) {
    // Arithmetic
    case PRIM_ADD: return prim_add(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_SUB: return prim_sub(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_MUL: return prim_mul(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_DIV: return prim_div(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_MOD: return prim_mod(HEAP[loc + 0], HEAP[loc + 1]);
    // Bitwise
    case PRIM_AND: return prim_and(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_OR:  return prim_or(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_XOR: return prim_xor(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_LSH: return prim_lsh(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_RSH: return prim_rsh(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_NOT: return prim_not(HEAP[loc + 0]);
    // Comparison
    case PRIM_EQ:  return prim_eq(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_NE:  return prim_ne(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_LT:  return prim_lt(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_LE:  return prim_le(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_GT:  return prim_gt(HEAP[loc + 0], HEAP[loc + 1]);
    case PRIM_GE:  return prim_ge(HEAP[loc + 0], HEAP[loc + 1]);
    // Dynamic label
    case PRIM_DUP: return prim_dup(HEAP[loc + 0], HEAP[loc + 1], HEAP[loc + 2]);
    case PRIM_SUP: return prim_sup(HEAP[loc + 0], HEAP[loc + 1], HEAP[loc + 2]);
    default: {
      fprintf(stderr, "unknown primitive: %u\n", nam);
      exit(1);
    }
  }
}
