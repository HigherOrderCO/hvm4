#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

// Types
// =====

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef u64 Term;

typedef struct {
  Term k0;
  Term k1;
} Copy;

// Function Definition Macro
// =========================

#define fn static inline

// Tags
// ====

#define NAM  0
#define DRY  1
#define REF  2
#define ALO  3
#define ERA  4
#define CO0  5
#define CO1  6
#define VAR  7
#define LAM  8
#define APP  9
#define SUP 10
#define DUP 11
#define MAT 12
#define C00 13
#define C01 14
#define C02 15
#define C03 16
#define C04 17
#define C05 18
#define C06 19
#define C07 20
#define C08 21
#define C09 22
#define C10 23
#define C11 24
#define C12 25
#define C13 26
#define C14 27
#define C15 28
#define C16 29
#define NUM 30

// Bit Layout
// ==========

#define SUB_BITS 1
#define TAG_BITS 7
#define EXT_BITS 24
#define VAL_BITS 32

#define SUB_SHIFT 63
#define TAG_SHIFT 56
#define EXT_SHIFT 32
#define VAL_SHIFT 0

#define SUB_MASK 0x1
#define TAG_MASK 0x7F
#define EXT_MASK 0xFFFFFF
#define VAL_MASK 0xFFFFFFFF

// Capacities
// ==========

#define HEAP_CAP (1ULL << 32)
#define BOOK_CAP (1ULL << 24)
#define WNF_CAP  (1ULL << 32)

// Heap Globals
// ============

static Term *HEAP;
static u64   ALLOC = 1;

// Book Globals
// ============

static u32 *BOOK;

// WNF Globals
// ===========

static Term *STACK;
static u32   S_POS = 1;
static u64   ITRS  = 0;
static int   DEBUG = 0;

// Nick Alphabet
// =============

static const char *nick_alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$";

// Parser Types
// ============

typedef struct {
  char *file;
  char *src;
  u32   pos;
  u32   len;
  u32   line;
  u32   col;
} PState;

typedef struct {
  u32 name;
  u32 depth;
  u32 lab;
} PBind;

// Parser Globals
// ==============

static char  *PARSE_SEEN_FILES[1024];
static u32    PARSE_SEEN_FILES_LEN = 0;
static PBind  PARSE_BINDS[16384];
static u32    PARSE_BINDS_LEN = 0;

// Term
// ====
#include "term/new.c"
#include "term/sub.c"
#include "term/tag.c"
#include "term/ext.c"
#include "term/val.c"
#include "term/arity.c"
#include "term/mark.c"
#include "term/unmark.c"

// Heap
// ====

#include "heap/alloc.c"

// Term Constructors
// =================

#include "term/new/_.c"
#include "term/new/nam.c"
#include "term/new/dry.c"
#include "term/new/var.c"
#include "term/new/ref.c"
#include "term/new/era.c"
#include "term/new/co0.c"
#include "term/new/co1.c"
#include "term/new/lam.c"
#include "term/new/app.c"
#include "term/new/sup.c"
#include "term/new/dup.c"
#include "term/new/mat.c"
#include "term/new/ctr.c"
#include "term/new/num.c"
#include "term/clone.c"

// Heap Substitution
// =================

#include "heap/subst_var.c"
#include "heap/subst_cop.c"

// Nick
// ====

#include "nick/letter_to_b64.c"
#include "nick/is_init.c"
#include "nick/is_char.c"

// System
// ======

#include "sys/error.c"
#include "sys/path_join.c"
#include "sys/file_read.c"

// Print
// =====

#include "print/name.c"
#include "print/term.c"

// Parse
// =====

#include "parse/error.c"
#include "parse/at_end.c"
#include "parse/peek_at.c"
#include "parse/peek.c"
#include "parse/advance.c"
#include "parse/starts_with.c"
#include "parse/match.c"
#include "parse/is_space.c"
#include "parse/skip_comment.c"
#include "parse/skip.c"
#include "parse/consume.c"
#include "parse/bind_push.c"
#include "parse/bind_pop.c"
#include "parse/bind_lookup.c"
#include "parse/name.c"
#include "parse/term/lam.c"
#include "parse/term/dup.c"
#include "parse/term/sup.c"
#include "parse/term/ctr.c"
#include "parse/term/ref.c"
#include "parse/term/par.c"
#include "parse/term/num.c"
#include "parse/term/var.c"
#include "parse/term/app.c"
#include "parse/term/_.c"
#include "parse/include.c"
#include "parse/def.c"

// WNF
// ===

#include "wnf/app_era.c"
#include "wnf/app_nam.c"
#include "wnf/app_dry.c"
#include "wnf/app_ctr.c"
#include "wnf/app_lam.c"
#include "wnf/app_sup.c"
#include "wnf/app_mat_sup.c"
#include "wnf/app_mat_ctr.c"
#include "wnf/dup_nam.c"
#include "wnf/dup_dry.c"
#include "wnf/dup_lam.c"
#include "wnf/dup_sup.c"
#include "wnf/dup_node.c"
#include "wnf/alo_var.c"
#include "wnf/alo_cop.c"
#include "wnf/alo_nam.c"
#include "wnf/alo_dry.c"
#include "wnf/alo_lam.c"
#include "wnf/alo_dup.c"
#include "wnf/alo_node.c"
#include "wnf/_.c"

// SNF
// ===

#include "snf/_.c"

// Collapse
// ========

#include "collapse/inject.c"
#include "collapse/_.c"
