// HVM4 Runtime Implementation in C
// =================================
//
// This file implements the HVM4, an Interaction Calculus runtime, ported from
// Haskell. It includes parsing, stringification, and a stack-based weak normal
// form (WNF) evaluator with all interaction rules.
//
// Term Pointer Layout (64-bit)
// ----------------------------
// | SUB  (1 bit)   ::= marks heap slot as containing a substitution
// | TAG  (7 bits)  ::= constructor variant (APP, LAM, SUP, etc.)
// | EXT  (24 bits) ::= dup label, ctr name, or ref name
// | VAL  (32 bits) ::= heap address or unboxed value
//
// Tag Encoding
// ------------
// - CO0/CO1: Two tags for Cop (copy) nodes, representing sides 0 and 1
// - CT0-CTG: Constructor tags encode arity directly (CT0+n for n fields, max 16)
// - Names (variable, constructor, reference) use 6-char base64 strings encoded
//   as 24-bit integers fitting in the EXT field
//
// Memory Model (No Separate Maps)
// -------------------------------
// Unlike the Haskell version which uses IntMaps for 'dups' and 'subs', this
// implementation stores everything directly on the heap:
//
// - DUP nodes: Stored inline on heap. CO0/CO1 point to a dup node holding the
//   duplicated expression (label stored in CO0/CO1's EXT field).
//
// - Substitutions: Stored where the lambda's body, or duplicator expression,
//   was. When app_lam fires, the argument replaces the lambda body slot. The
//   SUB bit distinguishes actual terms from substitutions, allowing VAR, CO0
//   and CO1 to detect whether their target is a binding node or a subst.
//
// Book vs Runtime Term Representation
// -----------------------------------
// Book terms (parsed definitions) use de Bruijn indices and are immutable:
//   - VAR: ext = 0         ; val = bru_index
//   - CO_: ext = dup_label ; val = bru_index
//   - LAM: ext = bru_depth ; val = body_location
//   - DUP: ext = dup_label ; val = expr_location
//
// Runtime terms (after ALO allocation) use heap locations:
//   - VAR : ext = 0         ; val = binding_lam_body_location
//   - CO_ : ext = dup_label ; val = binding_dup_expr_location
//   - LAM : ext = 0         ; val = expr_location
//   - DUP : ext = 0         ; val = expr_location
//
// ALO (Allocation) Nodes
// ----------------------
// ALO terms reference immutable book entries and lazily convert them to
// runtime terms. Each ALO stores a pair (bind_list, book_term_loc) packed
// into a single 64-bit heap word:
//   - Low 32 bits: book term location
//   - High 32 bits: bind list head (linked list of binder locations)
//
// The bind list maps de Bruijn levels to runtime heap locations of binding
// LAM/DUP nodes. When an ALO interaction occurs, one layer of the book term
// is extracted and converted to a runtime term.
//
// Stack-Based WNF Evaluator
// -------------------------
//   To avoid stack overflow, WNF uses an explicit stack with two phases:
//
//   REDUCE phase: Push eliminators onto stack and descend into their targets
//     - APP: push frame, enter function
//     - MAT: push frame, enter scrutinee (after MAT reaches head position)
//     - CO0/CO1: push frame, enter dup'd expression
//
//   APPLY phase: Pop frames and dispatch interactions based on WHNF result
//
//   DUP and ALO don't push stack frames since they immediately trigger their
//   respective interactions without requiring sub-WNF results first.
//
// Internal-Only Constructs
// ------------------------
// These nodes are internal and not parseable:
// - ALO: lazy alloc
// - NAM: stuck var
// - DRY: stuck app
//
// Style Guide
// -----------
// Abide to the guidelines below strictly!
//
// > NEVER write single-line ifs, loops, statements, functions.
//
//   Don't:
//     if { ... }
//     while { ... }
//     u32 foo(x) { ... }
//     foo(); bar();
//
//   Do:
//     if {
//       ...
//     }
//     while {
//       ...
//     }
//     u32 foo(x) {
//       ...
//     }
//     foo();
//     bar();
//
// > ALWAYS use switch for Term pattern matching.
//
//   Don't:
//     if (tag == FOO) {
//       ...
//     } else if (tag == BAR) {
//       ...
//     } ...
//
//   Do:
//     switch (tag) {
//       case FOO: {
//         ...
//       }
//       case BAR: {
//         ...
//       }
//     }
//
// > Aggressively abstract common patterns (DRY).
//
//   When a pattern is repeated in multiple places:
//
//   Don't:
//     fn Term <many_fns>(...) {
//       ...
//       if (side == 0) {
//         HEAP[loc] = mark_sub(res1);
//         return res0;
//       } else {
//         HEAP[loc] = mark_sub(res0);
//         return res1;
//       }
//    }
//
//   Do:
//     fn Term subst_dup(u8 side, u32 loc, Term r0, Term r1) {
//       HEAP[loc] = mark_sub(side == 0 ? r1 : r0);
//       return side == 0 ? r0 : r1;
//     }
//     fn Term <many_fns>(...) {
//       ...
//       return subst_dup(side, loc, res0, res1);
//     }
//
//   In general, spend some time reasoning about opportunities to apply the DRY
//   principle, extracting common patterns out to reduce code size. We greatly
//   appreciate simplicity brought by good abstractions!
//
// > Align columns whenever reasonable; adjust names as needed.
//
//   Don't:
//
//   Term abc = foo;
//   u32 x = 123;
//   Term the_amazing_cat = bar;
//
//   Do:
//
//   Term abc = foo;
//   u32  x   = 123;
//   Term cat = bar;
//
//   Don't:
//
//   foo[x] = 123;
//   foo[x+1] = 456;
//
//   Do:
//
//   foo[x+0] = 123;
//   foo[x+1] = 456;
//
// > Separate sessions with markdown-inspired headers.
//
//   Don't:
//
//   ---------------------------------
//   File Session
//   ---------------------------------
//
//   Do:
//
//   File Session
//   ============
//
//   File Sub-Session
//   ----------------
//
//   ### File Sub-Sub-Session

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
#define CT0 13
#define CT1 14
#define CT2 15
#define CT3 16
#define CT4 17
#define CT5 18
#define CT6 19
#define CT7 20
#define CT8 21
#define CT9 22
#define CTA 23
#define CTB 24
#define CTC 25
#define CTD 26
#define CTE 27
#define CTF 28
#define CTG 29

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

#define BOOK_CAP  (1ULL << 24)
#define HEAP_CAP  (1ULL << 32)
#define STACK_CAP (1ULL << 32)

// Globals
// =======

static u32  *BOOK;
static Term *HEAP;
static Term *STACK;

static u32 S_POS = 1;
static u64 ALLOC = 1;
static u64 ITRS  = 0;

static int DEBUG = 0;

// System Helpers
// ==============

fn void error(const char *msg) {
  fprintf(stderr, "ERROR: %s\n", msg);
  exit(1);
}

fn void path_join(char *out, int size, const char *base, const char *rel) {
  if (rel[0] == '/') {
    snprintf(out, size, "%s", rel);
    return;
  }
  const char *slash = strrchr(base, '/');
  if (slash) {
    snprintf(out, size, "%.*s/%s", (int)(slash - base), base, rel);
  } else {
    snprintf(out, size, "%s", rel);
  }
}

fn char *file_read(const char *path) {
  FILE *fp = fopen(path, "rb");
  if (!fp) {
    return NULL;
  }
  fseek(fp, 0, SEEK_END);
  long len = ftell(fp);
  fseek(fp, 0, SEEK_SET);
  char *src = malloc(len + 1);
  if (!src) {
    error("OOM");
  }
  fread(src, 1, len, fp);
  src[len] = 0;
  fclose(fp);
  return src;
}

// Term Helpers
// ============

fn Term new_term(u8 sub, u8 tag, u32 ext, u32 val) {
  return ((u64)sub << SUB_SHIFT)
       | ((u64)(tag & TAG_MASK) << TAG_SHIFT)
       | ((u64)(ext & EXT_MASK) << EXT_SHIFT)
       | ((u64)(val & VAL_MASK));
}

fn u8 sub_of(Term t) {
  return (t >> SUB_SHIFT) & SUB_MASK;
}

fn u8 tag_of(Term t) {
  return (t >> TAG_SHIFT) & TAG_MASK;
}

fn u32 ext_of(Term t) {
  return (t >> EXT_SHIFT) & EXT_MASK;
}

fn u32 val_of(Term t) {
  return (t >> VAL_SHIFT) & VAL_MASK;
}

fn Term mark_sub(Term t) {
  return t | ((u64)1 << SUB_SHIFT);
}

fn Term clear_sub(Term t) {
  return t & ~(((u64)SUB_MASK) << SUB_SHIFT);
}

fn u64 heap_alloc(u64 size) {
  if (ALLOC + size >= HEAP_CAP) {
    error("HEAP_OVERFLOW\n");
  }
  u64 at = ALLOC;
  ALLOC += size;
  return at;
}

// Names
// =====

static const char *alphabet = "_abcdefghijklmnopqrstuvwxyzABCfnGHIJKLMNOPQRSTUVWXYZ0123456789$";

fn int char_to_b64(char c) {
  if (c == '_') {
    return 0;
  }
  if (c >= 'a' && c <= 'z') {
    return 1 + (c - 'a');
  }
  if (c >= 'A' && c <= 'Z') {
    return 27 + (c - 'A');
  }
  if (c >= '0' && c <= '9') {
    return 53 + (c - '0');
  }
  if (c == '$') {
    return 63;
  }
  return -1;
}

fn int is_name_start(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

fn int is_name_char(char c) {
  return char_to_b64(c) >= 0;
}

// Term Constructors
// =================

fn Term New(u8 tag, u32 ext, u32 ari, Term *args) {
  u64 loc = heap_alloc(ari);
  for (u32 i = 0; i < ari; i++) {
    HEAP[loc + i] = args[i];
  }
  return new_term(0, tag, ext, loc);
}

fn Term Var(u32 loc) {
  return new_term(0, VAR, 0, loc);
}

fn Term Ref(u32 nam) {
  return new_term(0, REF, nam, 0);
}

fn Term Nam(u32 nam) {
  return new_term(0, NAM, 0, nam);
}

fn Term Era(void) {
  return new_term(0, ERA, 0, 0);
}

fn Term Co0(u32 lab, u32 loc) {
  return new_term(0, CO0, lab, loc);
}

fn Term Co1(u32 lab, u32 loc) {
  return new_term(0, CO1, lab, loc);
}

fn Term Lam(Term body) {
  return New(LAM, 0, 1, (Term[]){body});
}

fn Term App(Term fun, Term arg) {
  return New(APP, 0, 2, (Term[]){fun, arg});
}

fn Term Sup(u32 lab, Term tm0, Term tm1) {
  return New(SUP, lab, 2, (Term[]){tm0, tm1});
}

fn Term Dry(Term tm0, Term tm1) {
  return New(DRY, 0, 2, (Term[]){tm0, tm1});
}

fn Term Dup(u32 lab, Term val, Term body) {
  return New(DUP, lab, 2, (Term[]){val, body});
}

fn Term Mat(u32 nam, Term val, Term nxt) {
  return New(MAT, nam, 2, (Term[]){val, nxt});
}

fn Term Ctr(u32 nam, u32 ari, Term *args) {
  return New(CT0 + ari, nam, ari, args);
}

// Cloning
// =======

fn Copy clone(u32 lab, Term val) {
  u64 loc   = heap_alloc(1);
  HEAP[loc] = val;
  return (Copy){
    new_term(0, CO0, lab, loc),
    new_term(0, CO1, lab, loc)
  };
}

// Dup Substitution Helper
// -----------------------

fn Term subst_dup(u8 side, u32 loc, Term r0, Term r1) {
  HEAP[loc] = mark_sub(side == 0 ? r1 : r0);
  return side == 0 ? r0 : r1;
}

// Stringifier
// ===========

fn void print_name(u32 n) {
  if (n < 64) {
    putchar(alphabet[n]);
  } else {
    print_name(n / 64);
    putchar(alphabet[n % 64]);
  }
}

fn void print_term_go(Term term, u32 depth);

fn void print_term_go(Term term, u32 depth) {
  switch (tag_of(term)) {
    case VAR: {
      print_name(val_of(term));
      break;
    }
    case REF: {
      printf("@");
      print_name(ext_of(term));
      break;
    }
    case NAM: {
      print_name(val_of(term));
      break;
    }
    case ERA: {
      printf("&{}");
      break;
    }
    case CO0: {
      print_name(val_of(term));
      printf("₀");
      break;
    }
    case CO1: {
      print_name(val_of(term));
      printf("₁");
      break;
    }
    case LAM: {
      u32 loc = val_of(term);
      u32 nam = depth + 1;
      printf("λ");
      print_name(nam);
      printf(".");
      print_term_go(HEAP[loc], depth + 1);
      break;
    }
    case APP:
    case DRY: {
      Term spine[256];
      u32  len  = 0;
      Term curr = term;
      while ((tag_of(curr) == APP || tag_of(curr) == DRY) && len < 256) {
        u32 loc = val_of(curr);
        spine[len++] = HEAP[loc + 1];
        curr = HEAP[loc];
      }
      if (tag_of(curr) == LAM) {
        printf("(");
        print_term_go(curr, depth);
        printf(")");
      } else {
        print_term_go(curr, depth);
      }
      printf("(");
      for (u32 i = 0; i < len; i++) {
        if (i > 0) {
          printf(",");
        }
        print_term_go(spine[len - 1 - i], depth);
      }
      printf(")");
      break;
    }
    case SUP: {
      u32 loc = val_of(term);
      printf("&");
      print_name(ext_of(term));
      printf("{");
      print_term_go(HEAP[loc + 0], depth);
      printf(",");
      print_term_go(HEAP[loc + 1], depth);
      printf("}");
      break;
    }
    case DUP: {
      u32 loc = val_of(term);
      u32 nam = depth + 1;
      printf("!");
      print_name(nam);
      printf("&");
      print_name(ext_of(term));
      printf("=");
      print_term_go(HEAP[loc + 0], depth);
      printf(";");
      print_term_go(HEAP[loc + 1], depth + 1);
      break;
    }
    case MAT: {
      u32 loc = val_of(term);
      printf("λ{#");
      print_name(ext_of(term));
      printf(":");
      print_term_go(HEAP[loc + 0], depth);
      printf(";");
      print_term_go(HEAP[loc + 1], depth);
      printf("}");
      break;
    }
    case CT0 ... CTG: {
      u32 ari = tag_of(term) - CT0;
      u32 loc = val_of(term);
      printf("#");
      print_name(ext_of(term));
      printf("{");
      for (u32 i = 0; i < ari; i++) {
        if (i > 0) {
          printf(",");
        }
        print_term_go(HEAP[loc + i], depth);
      }
      printf("}");
      break;
    }
    case ALO: {
      printf("<ALO>");
      break;
    }
  }
}

fn void print_term(Term term) {
  print_term_go(term, 0);
}

// Parser
// ======

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
} PBind;

static char  *PARSE_SEEN_FILES[1024];
static u32    PARSE_SEEN_FILES_LEN = 0;
static PBind  PARSE_BINDS[16384];
static u32    PARSE_BINDS_LEN = 0;

fn void parse_error(PState *s, const char *expected, char detected) {
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m (%s:%d:%d)\n", s->file, s->line, s->col);
  fprintf(stderr, "- expected: %s\n", expected);
  if (detected == 0) {
    fprintf(stderr, "- detected: EOF\n");
  } else {
    fprintf(stderr, "- detected: '%c'\n", detected);
  }
  exit(1);
}

fn int at_end(PState *s) {
  return s->pos >= s->len;
}

fn char peek_at(PState *s, u32 offset) {
  u32 idx = s->pos + offset;
  return (idx >= s->len) ? 0 : s->src[idx];
}

fn char peek(PState *s) {
  return peek_at(s, 0);
}

fn void advance(PState *s) {
  if (at_end(s)) {
    return;
  }
  if (s->src[s->pos] == '\n') {
    s->line++;
    s->col = 1;
  } else {
    s->col++;
  }
  s->pos++;
}

fn int starts_with(PState *s, const char *str) {
  u32 i = 0;
  while (str[i]) {
    if (peek_at(s, i) != str[i]) {
      return 0;
    }
    i++;
  }
  return 1;
}

fn int match(PState *s, const char *str) {
  if (!starts_with(s, str)) {
    return 0;
  }
  while (*str) {
    advance(s);
    str++;
  }
  return 1;
}

fn int is_space(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

fn void skip_comment(PState *s) {
  while (!at_end(s) && peek(s) != '\n') {
    advance(s);
  }
}

fn void skip(PState *s) {
  while (!at_end(s)) {
    if (is_space(peek(s))) {
      advance(s);
      continue;
    }
    if (starts_with(s, "//")) {
      skip_comment(s);
      continue;
    }
    break;
  }
}

fn void consume(PState *s, const char *str) {
  skip(s);
  if (!match(s, str)) {
    parse_error(s, str, peek(s));
  }
  skip(s);
}

fn void bind_push(u32 name, u32 depth) {
  PARSE_BINDS[PARSE_BINDS_LEN++] = (PBind){name, depth};
}

fn void bind_pop(void) {
  PARSE_BINDS_LEN--;
}

fn int bind_lookup(u32 name, u32 depth) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    if (PARSE_BINDS[i].name == name) {
      return depth - 1 - PARSE_BINDS[i].depth;
    }
  }
  return -1;
}

fn u32 parse_name(PState *s) {
  skip(s);
  char c = peek(s);
  if (!is_name_start(c)) {
    parse_error(s, "name", c);
  }
  u32 k = 0;
  while (is_name_char(peek(s))) {
    c = peek(s);
    k = ((k << 6) + char_to_b64(c)) & EXT_MASK;
    advance(s);
  }
  skip(s);
  return k;
}

fn Term parse_term(PState *s, u32 depth);
fn void parse_def(PState *s);

fn Term parse_mat_body(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '}') {
    consume(s, "}");
    return Era();
  }
  if (peek(s) == '#') {
    consume(s, "#");
    u32  nam = parse_name(s);
    consume(s, ":");
    Term val = parse_term(s, depth);
    skip(s);
    match(s, ";");
    skip(s);
    Term nxt = parse_mat_body(s, depth);
    return Mat(nam, val, nxt);
  }
  Term val = parse_term(s, depth);
  consume(s, "}");
  return val;
}

fn Term parse_lam(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '{') {
    consume(s, "{");
    return parse_mat_body(s, depth);
  }
  u32 nam = parse_name(s);
  consume(s, ".");
  bind_push(nam, depth);
  u64  loc  = heap_alloc(1);
  Term body = parse_term(s, depth + 1);
  HEAP[loc] = body;
  bind_pop();
  return new_term(0, LAM, depth, loc);
}

fn Term parse_dup(PState *s, u32 depth) {
  u32 nam = parse_name(s);
  consume(s, "&");
  u32  lab = parse_name(s);
  consume(s, "=");
  Term val = parse_term(s, depth);
  skip(s);
  match(s, ";");
  skip(s);
  bind_push(nam, depth);
  u64 loc       = heap_alloc(2);
  HEAP[loc + 0] = val;
  Term body     = parse_term(s, depth + 1);
  HEAP[loc + 1] = body;
  bind_pop();
  return new_term(0, DUP, lab, loc);
}

fn Term parse_sup(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '{') {
    consume(s, "{");
    consume(s, "}");
    return Era();
  }
  u32 lab = parse_name(s);
  consume(s, "{");
  Term tm0 = parse_term(s, depth);
  skip(s);
  match(s, ",");
  skip(s);
  Term tm1 = parse_term(s, depth);
  consume(s, "}");
  return Sup(lab, tm0, tm1);
}

fn Term parse_ctr(PState *s, u32 depth) {
  u32  nam = parse_name(s);
  consume(s, "{");
  Term args[16];
  u32  cnt = 0;
  skip(s);
  if (peek(s) != '}') {
    while (1) {
      args[cnt++] = parse_term(s, depth);
      skip(s);
      if (peek(s) == ',') {
        consume(s, ",");
        continue;
      }
      break;
    }
  }
  consume(s, "}");
  return Ctr(nam, cnt, args);
}

fn Term parse_ref(PState *s) {
  skip(s);
  if (peek(s) == '{') {
    parse_error(s, "reference name", peek(s));
  }
  u32 nam = parse_name(s);
  return Ref(nam);
}

fn Term parse_par(PState *s, u32 depth) {
  Term term = parse_term(s, depth);
  consume(s, ")");
  return term;
}

fn Term parse_var(PState *s, u32 depth) {
  skip(s);
  u32 nam = parse_name(s);
  int idx = bind_lookup(nam, depth);
  skip(s);
  int side = match(s, "₀") ? 0 : match(s, "₁") ? 1 : -1;
  skip(s);
  u32 val = (idx >= 0) ? (u32)idx : nam;
  u8  tag = (side == 0) ? CO0 : (side == 1) ? CO1 : VAR;
  return new_term(0, tag, 0, val);
}

fn Term parse_app(Term f, PState *s, u32 depth) {
  skip(s);
  if (peek(s) != '(') {
    return f;
  }
  consume(s, "(");
  if (peek(s) == ')') {
    consume(s, ")");
    return parse_app(f, s, depth);
  }
  while (1) {
    Term arg = parse_term(s, depth);
    f = App(f, arg);
    skip(s);
    if (peek(s) == ',') {
      consume(s, ",");
      continue;
    }
    if (peek(s) == ')') {
      consume(s, ")");
      break;
    }
    parse_error(s, "',' or ')'", peek(s));
  }
  return parse_app(f, s, depth);
}

fn Term parse_term(PState *s, u32 depth) {
  skip(s);
  Term t;
  if (match(s, "λ")) {
    t = parse_lam(s, depth);
  } else if (match(s, "!")) {
    t = parse_dup(s, depth);
  } else if (match(s, "&")) {
    t = parse_sup(s, depth);
  } else if (match(s, "#")) {
    t = parse_ctr(s, depth);
  } else if (match(s, "@")) {
    t = parse_ref(s);
  } else if (match(s, "(")) {
    t = parse_par(s, depth);
  } else {
    t = parse_var(s, depth);
  }
  return parse_app(t, s, depth);
}

fn void do_include(PState *s, const char *filename) {
  char path[1024];
  path_join(path, sizeof(path), s->file, filename);
  for (u32 i = 0; i < PARSE_SEEN_FILES_LEN; i++) {
    if (strcmp(PARSE_SEEN_FILES[i], path) == 0) {
      return;
    }
  }
  if (PARSE_SEEN_FILES_LEN >= 1024) {
    error("MAX_INCLUDES");
  }
  PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN++] = strdup(path);
  char *src = file_read(path);
  if (!src) {
    fprintf(stderr, "Error: could not open '%s'\n", path);
    exit(1);
  }
  PState sub = {
    .file = PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN - 1],
    .src  = src,
    .pos  = 0,
    .len  = strlen(src),
    .line = 1,
    .col  = 1
  };
  parse_def(&sub);
  free(src);
}

fn void parse_include(PState *s) {
  skip(s);
  consume(s, "\"");
  u32 start = s->pos;
  while (peek(s) != '"' && !at_end(s)) {
    advance(s);
  }
  u32   end      = s->pos;
  consume(s, "\"");
  char *filename = malloc(end - start + 1);
  memcpy(filename, s->src + start, end - start);
  filename[end - start] = 0;
  do_include(s, filename);
  free(filename);
}

fn void parse_def(PState *s) {
  skip(s);
  if (at_end(s)) {
    return;
  }
  if (match(s, "#include")) {
    parse_include(s);
    parse_def(s);
    return;
  }
  if (match(s, "@")) {
    u32 nam = parse_name(s) & EXT_MASK;
    consume(s, "=");
    PARSE_BINDS_LEN = 0;
    Term val        = parse_term(s, 0);
    u64  loc        = heap_alloc(1);
    HEAP[loc]       = val;
    BOOK[nam]       = (u32)loc;
    parse_def(s);
    return;
  }
  parse_error(s, "definition or #include", peek(s));
}

// Beta Interactions
// =================

fn Term app_era(Term era, Term arg) {
  ITRS++;
  return Era();
}

fn Term app_nam(Term nam, Term arg) {
  ITRS++;
  return Dry(nam, arg);
}

fn Term app_dry(Term dry, Term arg) {
  ITRS++;
  return Dry(dry, arg);
}

fn Term app_lam(Term lam, Term arg) {
  ITRS++;
  u32  loc  = val_of(lam);
  Term body = HEAP[loc];
  HEAP[loc] = mark_sub(arg);
  return body;
}

fn Term app_sup(Term sup, Term arg) {
  ITRS++;
  u32  lab = ext_of(sup);
  u32  loc = val_of(sup);
  Term tm0 = HEAP[loc + 0];
  Term tm1 = HEAP[loc + 1];
  Copy A   = clone(lab, arg);
  return Sup(lab, App(tm0, A.k0), App(tm1, A.k1));
}

// Match Interactions
// ==================

fn Term app_mat_era(Term mat, Term arg) {
  ITRS++;
  return Era();
}

fn Term app_mat_sup(Term mat, Term sup) {
  ITRS++;
  u32  lab = ext_of(sup);
  Copy M   = clone(lab, mat);
  u32  loc = val_of(sup);
  Term a   = HEAP[loc + 0];
  Term b   = HEAP[loc + 1];
  return Sup(lab, App(M.k0, a), App(M.k1, b));
}

fn Term app_mat_ctr(Term mat, Term ctr) {
  ITRS++;
  u32 mat_nam = ext_of(mat);
  u32 ctr_nam = ext_of(ctr);
  u32 mat_loc = val_of(mat);
  u32 ctr_loc = val_of(ctr);
  u32 ari     = tag_of(ctr) - CT0;
  Term val    = HEAP[mat_loc + 0];
  Term nxt    = HEAP[mat_loc + 1];
  if (mat_nam == ctr_nam) {
    Term res = val;
    for (u32 i = 0; i < ari; i++) {
      res = App(res, HEAP[ctr_loc + i]);
    }
    return res;
  } else {
    return App(nxt, ctr);
  }
}

// Dup Interactions
// ================

fn Term dup_era(u32 lab, u32 loc, u8 side, Term era) {
  ITRS++;
  HEAP[loc] = mark_sub(Era());
  return Era();
}

fn Term dup_lam(u32 lab, u32 loc, u8 side, Term lam) {
  ITRS++;
  u32  lam_loc = val_of(lam);
  Term body    = HEAP[lam_loc];
  Copy B       = clone(lab, body);
  Term lam0    = Lam(B.k0);
  Term lam1    = Lam(B.k1);
  Term sup     = Sup(lab, Var(val_of(lam0)), Var(val_of(lam1)));
  HEAP[lam_loc] = mark_sub(sup);
  return subst_dup(side, loc, lam0, lam1);
}

fn Term dup_sup(u32 lab, u32 loc, u8 side, Term sup) {
  ITRS++;
  u32  sup_lab = ext_of(sup);
  u32  sup_loc = val_of(sup);
  Term tm0     = HEAP[sup_loc + 0];
  Term tm1     = HEAP[sup_loc + 1];
  if (lab == sup_lab) {
    return subst_dup(side, loc, tm0, tm1);
  } else {
    Copy A   = clone(lab, tm0);
    Copy B   = clone(lab, tm1);
    Term r0  = Sup(sup_lab, A.k0, B.k0);
    Term r1  = Sup(sup_lab, A.k1, B.k1);
    return subst_dup(side, loc, r0, r1);
  }
}

fn Term dup_ctr(u32 lab, u32 loc, u8 side, Term ctr) {
  ITRS++;
  u32  ari     = tag_of(ctr) - CT0;
  u32  ctr_nam = ext_of(ctr);
  u32  ctr_loc = val_of(ctr);
  Term args0[16], args1[16];
  for (u32 i = 0; i < ari; i++) {
    Copy A    = clone(lab, HEAP[ctr_loc + i]);
    args0[i]  = A.k0;
    args1[i]  = A.k1;
  }
  Term r0 = Ctr(ctr_nam, ari, args0);
  Term r1 = Ctr(ctr_nam, ari, args1);
  return subst_dup(side, loc, r0, r1);
}

fn Term dup_mat(u32 lab, u32 loc, u8 side, Term mat) {
  ITRS++;
  u32  mat_nam = ext_of(mat);
  u32  mat_loc = val_of(mat);
  Term val     = HEAP[mat_loc + 0];
  Term nxt     = HEAP[mat_loc + 1];
  Copy V       = clone(lab, val);
  Copy N       = clone(lab, nxt);
  Term r0      = Mat(mat_nam, V.k0, N.k0);
  Term r1      = Mat(mat_nam, V.k1, N.k1);
  return subst_dup(side, loc, r0, r1);
}

fn Term dup_nam(u32 lab, u32 loc, u8 side, Term nam) {
  ITRS++;
  HEAP[loc] = mark_sub(nam);
  return nam;
}

fn Term dup_dry(u32 lab, u32 loc, u8 side, Term dry) {
  ITRS++;
  u32  dry_loc = val_of(dry);
  Term tm0     = HEAP[dry_loc + 0];
  Term tm1     = HEAP[dry_loc + 1];
  Copy A       = clone(lab, tm0);
  Copy B       = clone(lab, tm1);
  Term r0      = Dry(A.k0, B.k0);
  Term r1      = Dry(A.k1, B.k1);
  return subst_dup(side, loc, r0, r1);
}

// Alloc Helpers
// =============

fn u32 bind_at(u32 ls_loc, u32 idx) {
  u32 cur = ls_loc;
  for (u32 i = 0; i < idx && cur != 0; i++) {
    cur = (u32)(HEAP[cur] >> 32);
  }
  return (cur != 0) ? (u32)(HEAP[cur] & 0xFFFFFFFF) : 0;
}

fn Term make_alo(u32 ls_loc, u32 tm_loc) {
  u64 loc   = heap_alloc(1);
  HEAP[loc] = ((u64)ls_loc << 32) | tm_loc;
  return new_term(0, ALO, 0, loc);
}

// Alloc Interactions
// ==================

fn Term alo_var(u32 ls_loc, u32 idx) {
  u32 bind = bind_at(ls_loc, idx);
  return bind ? Var(bind) : new_term(0, VAR, 0, idx);
}

fn Term alo_co0(u32 ls_loc, u32 lab, u32 idx) {
  u32 bind = bind_at(ls_loc, idx);
  return bind ? Co0(lab, bind) : new_term(0, CO0, lab, idx);
}

fn Term alo_co1(u32 ls_loc, u32 lab, u32 idx) {
  u32 bind = bind_at(ls_loc, idx);
  return bind ? Co1(lab, bind) : new_term(0, CO1, lab, idx);
}

fn Term alo_lam(u32 ls_loc, u32 book_body_loc) {
  u64 lam_body   = heap_alloc(1);
  u64 new_bind   = heap_alloc(1);
  HEAP[new_bind] = ((u64)ls_loc << 32) | (u32)lam_body;
  HEAP[lam_body] = make_alo(new_bind, book_body_loc);
  return new_term(0, LAM, 0, lam_body);
}

fn Term alo_app(u32 ls_loc, u32 app_loc) {
  return App(make_alo(ls_loc, app_loc + 0), make_alo(ls_loc, app_loc + 1));
}

fn Term alo_dup(u32 ls_loc, u32 book_loc, u32 lab) {
  u64 dup_val    = heap_alloc(1);
  u64 new_bind   = heap_alloc(1);
  HEAP[new_bind] = ((u64)ls_loc << 32) | (u32)dup_val;
  HEAP[dup_val]  = make_alo(ls_loc, book_loc + 0);
  return Dup(lab, make_alo(ls_loc, book_loc + 0), make_alo(new_bind, book_loc + 1));
}

fn Term alo_sup(u32 ls_loc, u32 sup_loc, u32 lab) {
  return Sup(lab, make_alo(ls_loc, sup_loc + 0), make_alo(ls_loc, sup_loc + 1));
}

fn Term alo_mat(u32 ls_loc, u32 mat_loc, u32 nam) {
  return Mat(nam, make_alo(ls_loc, mat_loc + 0), make_alo(ls_loc, mat_loc + 1));
}

fn Term alo_ctr(u32 ls_loc, u32 ctr_loc, u32 nam, u32 ari) {
  Term args[16];
  for (u32 i = 0; i < ari; i++) {
    args[i] = make_alo(ls_loc, ctr_loc + i);
  }
  return Ctr(nam, ari, args);
}

fn Term alo_dry(u32 ls_loc, u32 dry_loc) {
  return Dry(make_alo(ls_loc, dry_loc + 0), make_alo(ls_loc, dry_loc + 1));
}

// WNF
// ===

fn Term wnf(Term term) {
  S_POS = 0;
  Term next = term;
  Term whnf;

  enter: {
    if (DEBUG) {
      printf("wnf_enter: ");
      print_term(next);
      printf("\n");
    }

    switch (tag_of(next)) {
      case VAR: {
        u32 loc = val_of(next);
        if (sub_of(HEAP[loc])) {
          next = clear_sub(HEAP[loc]);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case CO0:
      case CO1: {
        u32 loc = val_of(next);
        if (sub_of(HEAP[loc])) {
          next = clear_sub(HEAP[loc]);
          goto enter;
        }
        Term dup_val = HEAP[loc];
        STACK[S_POS++] = next;
        next = dup_val;
        goto enter;
      }

      case APP: {
        u32  loc = val_of(next);
        Term fun = HEAP[loc];
        STACK[S_POS++] = next;
        next = fun;
        goto enter;
      }

      case DUP: {
        u32  loc  = val_of(next);
        Term body = HEAP[loc + 1];
        next = body;
        goto enter;
      }

      case REF: {
        u32 nam = ext_of(next);
        if (BOOK[nam] != 0) {
          next = make_alo(0, BOOK[nam]);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case ALO: {
        u32 alo_loc = val_of(next);
        u64 pair    = HEAP[alo_loc];
        u32 tm_loc  = (u32)(pair & 0xFFFFFFFF);
        u32 ls_loc  = (u32)(pair >> 32);
        Term book   = HEAP[tm_loc];

        switch (tag_of(book)) {
          case VAR: {
            next = alo_var(ls_loc, val_of(book));
            goto enter;
          }
          case CO0: {
            next = alo_co0(ls_loc, ext_of(book), val_of(book));
            goto enter;
          }
          case CO1: {
            next = alo_co1(ls_loc, ext_of(book), val_of(book));
            goto enter;
          }
          case LAM: {
            next = alo_lam(ls_loc, val_of(book));
            goto enter;
          }
          case APP: {
            next = alo_app(ls_loc, val_of(book));
            goto enter;
          }
          case DUP: {
            next = alo_dup(ls_loc, val_of(book), ext_of(book));
            goto enter;
          }
          case SUP: {
            next = alo_sup(ls_loc, val_of(book), ext_of(book));
            goto enter;
          }
          case MAT: {
            next = alo_mat(ls_loc, val_of(book), ext_of(book));
            goto enter;
          }
          case CT0 ... CTG: {
            next = alo_ctr(ls_loc, val_of(book), ext_of(book), tag_of(book) - CT0);
            goto enter;
          }
          case REF: {
            next = book;
            goto enter;
          }
          case ERA: {
            whnf = Era();
            goto apply;
          }
          case NAM: {
            whnf = book;
            goto apply;
          }
          case DRY: {
            next = alo_dry(ls_loc, val_of(book));
            goto enter;
          }
          case ALO: {
            whnf = next;
            goto apply;
          }
        }
        whnf = next;
        goto apply;
      }

      case NAM:
      case DRY:
      case ERA:
      case SUP:
      case LAM:
      case MAT:
      case CT0 ... CTG: {
        whnf = next;
        goto apply;
      }

      default: {
        whnf = next;
        goto apply;
      }
    }
  }

  apply: {
    if (DEBUG) {
      printf("wnf_apply: ");
      print_term(whnf);
      printf("\n");
    }

    while (S_POS > 0) {
      Term frame = STACK[--S_POS];

      switch (tag_of(frame)) {
        case APP: {
          u32  loc = val_of(frame);
          Term arg = HEAP[loc + 1];

          switch (tag_of(whnf)) {
            case ERA: {
              whnf = app_era(whnf, arg);
              continue;
            }
            case NAM: {
              whnf = app_nam(whnf, arg);
              continue;
            }
            case DRY: {
              whnf = app_dry(whnf, arg);
              continue;
            }
            case LAM: {
              whnf = app_lam(whnf, arg);
              next = whnf;
              goto enter;
            }
            case SUP: {
              whnf = app_sup(whnf, arg);
              next = whnf;
              goto enter;
            }
            case MAT: {
              STACK[S_POS++] = whnf;
              next = arg;
              goto enter;
            }
            default: {
              whnf = App(whnf, arg);
              continue;
            }
          }
        }

        case MAT: {
          Term mat = frame;
          switch (tag_of(whnf)) {
            case ERA: {
              whnf = app_mat_era(mat, whnf);
              continue;
            }
            case SUP: {
              whnf = app_mat_sup(mat, whnf);
              next = whnf;
              goto enter;
            }
            case CT0 ... CTG: {
              whnf = app_mat_ctr(mat, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              whnf = App(mat, whnf);
              continue;
            }
          }
        }

        case CO0:
        case CO1: {
          u8  side = (tag_of(frame) == CO0) ? 0 : 1;
          u32 loc  = val_of(frame);
          u32 lab  = ext_of(frame);

          switch (tag_of(whnf)) {
            case ERA: {
              whnf = dup_era(lab, loc, side, whnf);
              continue;
            }
            case LAM: {
              whnf = dup_lam(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case SUP: {
              whnf = dup_sup(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case CT0 ... CTG: {
              whnf = dup_ctr(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case MAT: {
              whnf = dup_mat(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case NAM: {
              whnf = dup_nam(lab, loc, side, whnf);
              continue;
            }
            case DRY: {
              whnf = dup_dry(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              u64 new_loc    = heap_alloc(1);
              HEAP[new_loc]  = whnf;
              u8  other_side = side == 0 ? 1 : 0;
              HEAP[loc]      = mark_sub(new_term(0, side == 0 ? CO1 : CO0, lab, new_loc));
              whnf           = new_term(0, side == 0 ? CO0 : CO1, lab, new_loc);
              continue;
            }
          }
        }

        default: {
          continue;
        }
      }
    }
  }

  return whnf;
}

// SNF
// ===

fn Term snf(Term term, u32 depth) {
  term = wnf(term);
  switch (tag_of(term)) {
    case VAR:
    case REF:
    case NAM:
    case ERA:
    case CO0:
    case CO1: {
      return term;
    }
    case LAM: {
      u64  loc  = val_of(term);
      Term body = HEAP[loc];
      HEAP[loc] = mark_sub(Nam(depth + 1));
      body      = snf(body, depth + 1);
      HEAP[loc] = body;
      return term;
    }
    case APP:
    case MAT:
    case SUP:
    case DRY: {
      u64 loc       = val_of(term);
      HEAP[loc + 0] = snf(HEAP[loc + 0], depth);
      HEAP[loc + 1] = snf(HEAP[loc + 1], depth);
      return term;
    }
    case DUP: {
      printf("TODO\n");
      abort();
    }
    case CT0 ... CTG: {
      u32 ari = tag_of(term) - CT0;
      u64 loc = val_of(term);
      for (u32 i = 0; i < ari; i++) {
        HEAP[loc + i] = snf(HEAP[loc + i], depth);
      }
      return term;
    }
    case ALO: {
      return term;
    }
    default: {
      return term;
    }
  }
}

// Main
// ====

int main(void) {
  BOOK  = calloc(BOOK_CAP, sizeof(u32));
  HEAP  = calloc(HEAP_CAP, sizeof(Term));
  STACK = calloc(STACK_CAP, sizeof(Term));

  if (!BOOK || !HEAP || !STACK) {
    error("Memory allocation failed");
  }

  const char *source =
    "@ctru = λt. λf. t\n"
    "@cfal = λt. λf. f\n"
    "@cnot = λb. λt. λf. b(f, t)\n"
    "@main = @cnot(@cnot(@ctru))\n";

  PState s = {
    .file = "inline",
    .src  = (char*)source,
    .pos  = 0,
    .len  = strlen(source),
    .line = 1,
    .col  = 1
  };
  parse_def(&s);

  u32 main_name = 0;
  const char *p = "main";
  while (*p) {
    main_name = ((main_name << 6) + char_to_b64(*p)) & EXT_MASK;
    p++;
  }

  if (BOOK[main_name] == 0) {
    error("@main not found");
  }

  Term main_term = HEAP[BOOK[main_name]];

  clock_t start = clock();
  Term result   = snf(main_term, 0);
  clock_t end   = clock();

  double time_sec = (double)(end - start) / CLOCKS_PER_SEC;

  print_term(result);
  printf("\n");
  printf("- Itrs: %llu interactions\n", (unsigned long long)ITRS);
  printf("- Time: %.6f seconds\n", time_sec);
  if (time_sec > 0) {
    printf("- Perf: %.0f interactions/second\n", (double)ITRS / time_sec);
  } else {
    printf("- Perf: N/A (too fast to measure)\n");
  }

  free(HEAP);
  free(BOOK);
  free(STACK);

  return 0;
}
