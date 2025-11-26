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
// - CTR...CTR+CTR_MAX_ARI: Constructor tags encode arity directly (CTR+n for n fields)
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
// Collapse Function
// -----------------
// Extracts superpositions (SUP) to the top level. For each term type:
// 1. Collapse subterms recursively
// 2. Build a template: nested lambdas that reconstruct the term
// 3. Call inject(template, collapsed_subterms)
// This will move the term to inside SUP layers, 'collapsing' it.
//
// Key: VARs in templates must point to their binding lambda's body location.
// For LAM, the inner lambda MUST reuse lam_loc so existing VARs stay bound.
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
//         subst_var(loc, res1);
//         return res0;
//       } else {
//         subst_var(loc, res0);
//         return res1;
//       }
//    }
//
//   Do:
//     fn Term subst_cop(u8 side, u32 loc, Term r0, Term r1) {
//       subst_var(loc, side == 0 ? r1 : r0);
//       return side == 0 ? r0 : r1;
//     }
//     fn Term <many_fns>(...) {
//       ...
//       return subst_cop(side, loc, res0, res1);
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
#define CTR 13
#define CTR_MAX_ARI 16

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

fn u8 tag(Term t) {
  return (t >> TAG_SHIFT) & TAG_MASK;
}

fn u32 ext(Term t) {
  return (t >> EXT_SHIFT) & EXT_MASK;
}

fn u32 val(Term t) {
  return (t >> VAL_SHIFT) & VAL_MASK;
}

fn u32 arity_of(Term t) {
  switch (tag(t)) {
    case LAM: {
      return 1;
    }
    case APP:
    case SUP:
    case DUP:
    case MAT:
    case DRY: {
      return 2;
    }
    case CTR ... CTR + CTR_MAX_ARI: {
      return tag(t) - CTR;
    }
    default: {
      return 0;
    }
  }
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

static const char *alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$";

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
  return New(CTR + ari, nam, ari, args);
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

fn void clone_many(u32 lab, Term *src, u32 n, Term *dst0, Term *dst1) {
  for (u32 i = 0; i < n; i++) {
    Copy c  = clone(lab, src[i]);
    dst0[i] = c.k0;
    dst1[i] = c.k1;
  }
}

// Substitution Helpers
// --------------------

fn void subst_var(u32 loc, Term val) {
  HEAP[loc] = mark_sub(val);
}

fn Term subst_cop(u8 side, u32 loc, Term r0, Term r1) {
  HEAP[loc] = mark_sub(side == 0 ? r1 : r0);
  return side == 0 ? r0 : r1;
}

// Stringifier
// ===========
//
// Unified term stringification with two output modes:
// - STR_LOG: print to stdout
// - STR_BUF: write to TERM_BUF

#define STR_LOG 0
#define STR_BUF 1

static u8    STR_MODE    = STR_LOG;
static char *TERM_BUF    = NULL;
static u32   TERM_BUF_POS = 0;
static u32   TERM_BUF_CAP = 0;

fn void str_putc(char c) {
  if (STR_MODE == STR_LOG) {
    putchar(c);
  } else {
    if (TERM_BUF_POS + 1 >= TERM_BUF_CAP) {
      TERM_BUF_CAP *= 2;
      TERM_BUF = realloc(TERM_BUF, TERM_BUF_CAP);
    }
    TERM_BUF[TERM_BUF_POS++] = c;
    TERM_BUF[TERM_BUF_POS]   = 0;
  }
}

fn void str_puts(const char *s) {
  while (*s) {
    str_putc(*s++);
  }
}

fn void str_name(u32 n) {
  if (n < 64) {
    str_putc(alphabet[n]);
  } else {
    str_name(n / 64);
    str_putc(alphabet[n % 64]);
  }
}

fn void str_term_go(Term term, u32 depth);

fn void str_term_go(Term term, u32 depth) {
  switch (tag(term)) {
    case VAR:
    case NAM: {
      str_name(val(term));
      break;
    }
    case REF: {
      str_putc('@');
      str_name(ext(term));
      break;
    }
    case ERA: {
      str_puts("&{}");
      break;
    }
    case CO0:
    case CO1: {
      str_name(val(term));
      str_puts(tag(term) == CO0 ? "₀" : "₁");
      break;
    }
    case LAM: {
      u32 loc = val(term);
      u32 nam = depth + 1;
      str_puts("λ");
      str_name(nam);
      str_putc('.');
      str_term_go(HEAP[loc], depth + 1);
      break;
    }
    case APP:
    case DRY: {
      Term spine[256];
      u32  len  = 0;
      Term curr = term;
      while ((tag(curr) == APP || tag(curr) == DRY) && len < 256) {
        u32 loc = val(curr);
        spine[len++] = HEAP[loc + 1];
        curr = HEAP[loc];
      }
      if (tag(curr) == LAM) {
        str_putc('(');
        str_term_go(curr, depth);
        str_putc(')');
      } else {
        str_term_go(curr, depth);
      }
      str_putc('(');
      for (u32 i = 0; i < len; i++) {
        if (i > 0) {
          str_putc(',');
        }
        str_term_go(spine[len - 1 - i], depth);
      }
      str_putc(')');
      break;
    }
    case SUP: {
      u32 loc = val(term);
      str_putc('&');
      str_name(ext(term));
      str_putc('{');
      str_term_go(HEAP[loc + 0], depth);
      str_putc(',');
      str_term_go(HEAP[loc + 1], depth);
      str_putc('}');
      break;
    }
    case DUP: {
      u32 loc = val(term);
      u32 nam = depth + 1;
      str_putc('!');
      str_name(nam);
      str_putc('&');
      str_name(ext(term));
      str_putc('=');
      str_term_go(HEAP[loc + 0], depth);
      str_putc(';');
      str_term_go(HEAP[loc + 1], depth + 1);
      break;
    }
    case MAT: {
      u32 loc = val(term);
      str_puts("λ{#");
      str_name(ext(term));
      str_putc(':');
      str_term_go(HEAP[loc + 0], depth);
      str_putc(';');
      str_term_go(HEAP[loc + 1], depth);
      str_putc('}');
      break;
    }
    case CTR ... CTR + CTR_MAX_ARI: {
      u32 ari = tag(term) - CTR;
      u32 loc = val(term);
      str_putc('#');
      str_name(ext(term));
      str_putc('{');
      for (u32 i = 0; i < ari; i++) {
        if (i > 0) {
          str_putc(',');
        }
        str_term_go(HEAP[loc + i], depth);
      }
      str_putc('}');
      break;
    }
    case ALO: {
      str_puts("<ALO>");
      break;
    }
  }
}

fn void print_term(Term term) {
  STR_MODE = STR_LOG;
  str_term_go(term, 0);
}

fn void term_buf_init(void) {
  TERM_BUF_CAP = 65536;
  TERM_BUF     = malloc(TERM_BUF_CAP);
  TERM_BUF_POS = 0;
}

fn void term_buf_free(void) {
  free(TERM_BUF);
  TERM_BUF     = NULL;
  TERM_BUF_POS = 0;
  TERM_BUF_CAP = 0;
}

fn char *term_to_str(Term term) {
  STR_MODE     = STR_BUF;
  TERM_BUF_POS = 0;
  str_term_go(term, 0);
  return TERM_BUF;
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
  u32 lab;
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

fn void bind_push(u32 name, u32 depth, u32 lab) {
  PARSE_BINDS[PARSE_BINDS_LEN++] = (PBind){name, depth, lab};
}

fn void bind_pop(void) {
  PARSE_BINDS_LEN--;
}

fn void bind_lookup(u32 name, u32 depth, int *idx, u32 *lab) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    if (PARSE_BINDS[i].name == name) {
      *idx = depth - 1 - PARSE_BINDS[i].depth;
      *lab = PARSE_BINDS[i].lab;
      return;
    }
  }
  *idx = -1;
  *lab = 0;
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
  bind_push(nam, depth, 0);
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
  bind_push(nam, depth, lab);
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
  return Ref(parse_name(s));
}

fn Term parse_par(PState *s, u32 depth) {
  Term term = parse_term(s, depth);
  consume(s, ")");
  return term;
}

fn Term parse_var(PState *s, u32 depth) {
  skip(s);
  u32 nam = parse_name(s);
  int idx;
  u32 lab;
  bind_lookup(nam, depth, &idx, &lab);
  skip(s);
  int side = match(s, "₀") ? 0 : match(s, "₁") ? 1 : -1;
  skip(s);
  u32 val = (idx >= 0) ? (u32)idx : nam;
  u8  tag = (side == 0) ? CO0 : (side == 1) ? CO1 : VAR;
  return new_term(0, tag, lab, val);
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

fn void parse_include(PState *s) {
  // Parse filename
  skip(s);
  consume(s, "\"");
  u32 start = s->pos;
  while (peek(s) != '"' && !at_end(s)) {
    advance(s);
  }
  u32 len = s->pos - start;
  consume(s, "\"");

  // Resolve path
  char filename[256], path[1024];
  memcpy(filename, s->src + start, len);
  filename[len] = 0;
  path_join(path, sizeof(path), s->file, filename);

  // Check if already included
  for (u32 i = 0; i < PARSE_SEEN_FILES_LEN; i++) {
    if (strcmp(PARSE_SEEN_FILES[i], path) == 0) {
      return;
    }
  }
  if (PARSE_SEEN_FILES_LEN >= 1024) {
    error("MAX_INCLUDES");
  }
  PARSE_SEEN_FILES[PARSE_SEEN_FILES_LEN++] = strdup(path);

  // Read and parse
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

fn Term app_era(void) {
  ITRS++;
  return Era();
}

fn Term app_stuck(Term fun, Term arg) {
  ITRS++;
  return Dry(fun, arg);
}

fn Term app_lam(Term lam, Term arg) {
  ITRS++;
  u32  loc  = val(lam);
  Term body = HEAP[loc];
  subst_var(loc, arg);
  return body;
}

fn Term app_sup(Term sup, Term arg) {
  ITRS++;
  u32  lab = ext(sup);
  u32  loc = val(sup);
  Term tm0 = HEAP[loc + 0];
  Term tm1 = HEAP[loc + 1];
  Copy A   = clone(lab, arg);
  return Sup(lab, App(tm0, A.k0), App(tm1, A.k1));
}

// Match Interactions
// ==================

fn Term app_mat_sup(Term mat, Term sup) {
  ITRS++;
  u32  lab = ext(sup);
  Copy M   = clone(lab, mat);
  u32  loc = val(sup);
  Term a   = HEAP[loc + 0];
  Term b   = HEAP[loc + 1];
  return Sup(lab, App(M.k0, a), App(M.k1, b));
}

fn Term app_mat_ctr(Term mat, Term ctr) {
  ITRS++;
  u32 ari = tag(ctr) - CTR;
  if (ext(mat) == ext(ctr)) {
    Term res = HEAP[val(mat)];
    for (u32 i = 0; i < ari; i++) {
      res = App(res, HEAP[val(ctr) + i]);
    }
    return res;
  } else {
    return App(HEAP[val(mat) + 1], ctr);
  }
}

// Dup Interactions
// ================

fn Term dup_lam(u32 lab, u32 loc, u8 side, Term lam) {
  ITRS++;
  Copy B   = clone(lab, HEAP[val(lam)]);
  Term l0  = Lam(B.k0);
  Term l1  = Lam(B.k1);
  subst_var(val(lam), Sup(lab, Var(val(l0)), Var(val(l1))));
  return subst_cop(side, loc, l0, l1);
}

fn Term dup_sup(u32 lab, u32 loc, u8 side, Term sup) {
  ITRS++;
  Term tm0 = HEAP[val(sup) + 0];
  Term tm1 = HEAP[val(sup) + 1];
  if (lab == ext(sup)) {
    return subst_cop(side, loc, tm0, tm1);
  } else {
    Copy A  = clone(lab, tm0);
    Copy B  = clone(lab, tm1);
    Term r0 = Sup(ext(sup), A.k0, B.k0);
    Term r1 = Sup(ext(sup), A.k1, B.k1);
    return subst_cop(side, loc, r0, r1);
  }
}

fn Term dup_node(u32 lab, u32 loc, u8 side, Term term) {
  ITRS++;
  u32 ari = arity_of(term);
  if (ari == 0) {
    subst_var(loc, term);
    return term;
  }
  u32  t_loc = val(term);
  u32  t_ext = ext(term);
  u8   t_tag = tag(term);
  Term args0[16], args1[16];
  for (u32 i = 0; i < ari; i++) {
    Copy A   = clone(lab, HEAP[t_loc + i]);
    args0[i] = A.k0;
    args1[i] = A.k1;
  }
  Term r0 = New(t_tag, t_ext, ari, args0);
  Term r1 = New(t_tag, t_ext, ari, args1);
  return subst_cop(side, loc, r0, r1);
}

// Alloc Helpers
// =============

fn u32 bind_at(u32 ls, u32 idx) {
  for (u32 i = 0; i < idx && ls != 0; i++) {
    ls = (u32)(HEAP[ls] & 0xFFFFFFFF);
  }
  return (ls != 0) ? (u32)(HEAP[ls] >> 32) : 0;
}

fn u32 make_bind(u32 tail, u32 loc) {
  u64 entry = heap_alloc(1);
  HEAP[entry] = ((u64)loc << 32) | tail;
  return (u32)entry;
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

fn Term alo_cop(u32 ls_loc, u32 idx, u32 lab, u8 side) {
  u32 bind = bind_at(ls_loc, idx);
  u8  tag  = side == 0 ? CO0 : CO1;
  return bind ? new_term(0, tag, lab, bind) : new_term(0, tag, lab, idx);
}

fn Term alo_lam(u32 ls_loc, u32 book_body_loc) {
  u64 lam_body  = heap_alloc(1);
  u32 new_bind  = make_bind(ls_loc, (u32)lam_body);
  HEAP[lam_body] = make_alo(new_bind, book_body_loc);
  return new_term(0, LAM, 0, lam_body);
}

fn Term alo_dup(u32 ls_loc, u32 book_loc, u32 lab) {
  u64 dup_val  = heap_alloc(1);
  u32 new_bind = make_bind(ls_loc, (u32)dup_val);
  HEAP[dup_val] = make_alo(ls_loc, book_loc + 0);
  return Dup(lab, make_alo(ls_loc, book_loc + 0), make_alo(new_bind, book_loc + 1));
}

fn Term alo_node(u32 ls_loc, u32 loc, u8 tag, u32 ext, u32 ari) {
  Term args[16];
  for (u32 i = 0; i < ari; i++) {
    args[i] = make_alo(ls_loc, loc + i);
  }
  return New(tag, ext, ari, args);
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

    switch (tag(next)) {
      case VAR: {
        u32 loc = val(next);
        if (sub_of(HEAP[loc])) {
          next = clear_sub(HEAP[loc]);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case CO0:
      case CO1: {
        u32 loc = val(next);
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
        u32  loc = val(next);
        Term fun = HEAP[loc];
        STACK[S_POS++] = next;
        next = fun;
        goto enter;
      }

      case DUP: {
        u32  loc  = val(next);
        Term body = HEAP[loc + 1];
        next = body;
        goto enter;
      }

      case REF: {
        u32 nam = ext(next);
        if (BOOK[nam] != 0) {
          next = make_alo(0, BOOK[nam]);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case ALO: {
        u32  alo_loc = val(next);
        u64  pair    = HEAP[alo_loc];
        u32  tm_loc  = (u32)(pair & 0xFFFFFFFF);
        u32  ls_loc  = (u32)(pair >> 32);
        Term book    = HEAP[tm_loc];

        switch (tag(book)) {
          case VAR: {
            next = alo_var(ls_loc, val(book));
            goto enter;
          }
          case CO0:
          case CO1: {
            next = alo_cop(ls_loc, val(book), ext(book), tag(book) == CO0 ? 0 : 1);
            goto enter;
          }
          case LAM: {
            next = alo_lam(ls_loc, val(book));
            goto enter;
          }
          case APP:
          case SUP:
          case MAT:
          case DRY:
          case CTR ... CTR + CTR_MAX_ARI: {
            next = alo_node(ls_loc, val(book), tag(book), ext(book), arity_of(book));
            goto enter;
          }
          case DUP: {
            next = alo_dup(ls_loc, val(book), ext(book));
            goto enter;
          }
          case REF:
          case NAM:
          case ERA: {
            next = book;
            goto enter;
          }
        }
      }

      case NAM:
      case DRY:
      case ERA:
      case SUP:
      case LAM:
      case MAT:
      case CTR ... CTR + CTR_MAX_ARI: {
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

      switch (tag(frame)) {
        case APP: {
          u32  loc = val(frame);
          Term arg = HEAP[loc + 1];

          switch (tag(whnf)) {
            case ERA: {
              whnf = app_era();
              continue;
            }
            case NAM:
            case DRY: {
              whnf = app_stuck(whnf, arg);
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
          switch (tag(whnf)) {
            case ERA: {
              whnf = app_era();
              continue;
            }
            case SUP: {
              whnf = app_mat_sup(mat, whnf);
              next = whnf;
              goto enter;
            }
            case CTR ... CTR + CTR_MAX_ARI: {
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
          u8  side = (tag(frame) == CO0) ? 0 : 1;
          u32 loc  = val(frame);
          u32 lab  = ext(frame);

          switch (tag(whnf)) {
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
            case ERA:
            case NAM: {
              whnf = dup_node(lab, loc, side, whnf);
              continue;
            }
            case MAT:
            case DRY:
            case CTR ... CTR + CTR_MAX_ARI: {
              whnf = dup_node(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              u64 new_loc   = heap_alloc(1);
              HEAP[new_loc] = whnf;
              subst_var(loc, new_term(0, side == 0 ? CO1 : CO0, lab, new_loc));
              whnf          = new_term(0, side == 0 ? CO0 : CO1, lab, new_loc);
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
  u32 ari = arity_of(term);
  if (ari == 0) {
    return term;
  }
  u64 loc = val(term);
  if (tag(term) == LAM) {
    Term body = HEAP[loc];
    subst_var(loc, Nam(depth + 1));
    HEAP[loc] = snf(body, depth + 1);
  } else {
    for (u32 i = 0; i < ari; i++) {
      HEAP[loc + i] = snf(HEAP[loc + i], depth);
    }
  }
  return term;
}

// Collapse
// ========
//
// Collapse brings all SUPs to the top level of a term. This is needed for
// observing superpositions (e.g., enumerating all possibilities).
//
// The algorithm works as follows:
// 1. WNF the term first
// 2. For SUP: recursively collapse both branches, keep SUP at top
// 3. For other compound terms: collapse all subterms, then use inject
//    to distribute any SUPs that appear in subterms
//
// inject(template, [args]) applies args to template using App nodes.
// When an arg is a SUP, it clones the template and remaining args,
// distributing the SUP to create two branches.

// Forward declarations
fn Term collapse(Term term);
fn Term inject(Term template, Term *args, u32 n_args);

// inject: Apply a list of collapsed arguments to a template.
// If any argument is a SUP, clone template and remaining args, distribute SUP.
fn Term inject(Term template, Term *args, u32 n_args) {
  if (n_args == 0) {
    return template;
  }

  Term head = wnf(args[0]);

  if (tag(head) == SUP) {
    // SUP found - distribute it
    u32  lab      = ext(head);
    u64  sup_loc  = val(head);
    Term sup_a    = HEAP[sup_loc + 0];
    Term sup_b    = HEAP[sup_loc + 1];

    // Clone the template and remaining arguments
    Copy T = clone(lab, template);
    Term args0[16], args1[16];
    args0[0] = sup_a;
    args1[0] = sup_b;
    clone_many(lab, args + 1, n_args - 1, args0 + 1, args1 + 1);

    // Recursively inject both branches
    Term r0 = inject(T.k0, args0, n_args);
    Term r1 = inject(T.k1, args1, n_args);

    return Sup(lab, r0, r1);
  } else {
    // Not a SUP - apply it and continue with remaining args
    Term applied = App(template, head);
    return inject(applied, args + 1, n_args - 1);
  }
}

// collapse: Bring all SUPs to the top level
fn Term collapse(Term term) {
  term = wnf(term);

  switch (tag(term)) {
    case ERA:
    case VAR:
    case REF:
    case NAM:
    case CO0:
    case CO1: {
      return term;
    }

    case SUP: {
      // Recursively collapse both branches, keep SUP at top
      u64  loc = val(term);
      Term a   = collapse(HEAP[loc + 0]);
      Term b   = collapse(HEAP[loc + 1]);
      return Sup(ext(term), a, b);
    }

    case LAM: {
      // Haskell: fV <- fresh; f' <- collapse f; inject (Lam fV (Lam k (Var fV))) [f']
      u64  lam_loc = val(term);
      Term body    = HEAP[lam_loc];

      // Collapse the body
      Term body_collapsed = collapse(body);

      // Build template: λfV. (λk. fV)
      // - outer lambda binds fV, body location = outer_loc
      // - inner lambda binds k (original), body location = lam_loc
      // - inner body = Var fV = VAR(outer_loc)
      u64 outer_loc = heap_alloc(1);
      HEAP[lam_loc] = new_term(0, VAR, 0, outer_loc);  // inner body = Var fV
      Term inner_lam = new_term(0, LAM, 0, lam_loc);   // inner lambda (Lam k ...)
      HEAP[outer_loc] = inner_lam;                     // outer body = inner lambda
      Term template = new_term(0, LAM, 0, outer_loc);  // outer lambda (Lam fV ...)

      Term args[1] = { body_collapsed };
      return inject(template, args, 1);
    }

    case APP:
    case DRY:
    case MAT: {
      // Template: λaV. λbV. T(aV, bV) where T is APP/DRY/MAT
      u64  loc = val(term);
      Term a   = collapse(HEAP[loc + 0]);
      Term b   = collapse(HEAP[loc + 1]);

      u64 aV_loc = heap_alloc(1);
      u64 bV_loc = heap_alloc(1);
      Term aV = new_term(0, VAR, 0, aV_loc);
      Term bV = new_term(0, VAR, 0, bV_loc);

      Term inner;
      switch (tag(term)) {
        case APP: {
          inner = App(aV, bV);
          break;
        }
        case DRY: {
          inner = Dry(aV, bV);
          break;
        }
        case MAT: {
          inner = Mat(ext(term), aV, bV);
          break;
        }
        default: {
          inner = App(aV, bV);
          break;
        }
      }

      HEAP[bV_loc] = inner;
      Term inner_lam = new_term(0, LAM, 0, bV_loc);
      HEAP[aV_loc] = inner_lam;
      Term template = new_term(0, LAM, 0, aV_loc);

      Term args[2] = { a, b };
      return inject(template, args, 2);
    }

    case CTR ... CTR + CTR_MAX_ARI: {
      // Haskell: inject (foldr Lam (Ctr k (map Var vs)) vs) as
      // Template: λv0. λv1. ... Ctr(Var v0, Var v1, ...)
      u32 ari = tag(term) - CTR;
      u32 nam = ext(term);
      u64 loc = val(term);

      if (ari == 0) {
        return term;
      }

      // Collapse all fields
      Term collapsed[16];
      for (u32 i = 0; i < ari; i++) {
        collapsed[i] = collapse(HEAP[loc + i]);
      }

      // Allocate lambda body locations (these are also the var binding points)
      u64 lam_locs[16];
      for (u32 i = 0; i < ari; i++) {
        lam_locs[i] = heap_alloc(1);
      }

      // Build vars pointing to their respective lambda body locations
      Term vars[16];
      for (u32 i = 0; i < ari; i++) {
        vars[i] = new_term(0, VAR, 0, lam_locs[i]);
      }

      // Build the Ctr with vars
      Term ctr = Ctr(nam, ari, vars);

      // Build nested lambdas from inside out
      // λv0. (λv1. (... (Ctr ...)))
      // Last lambda (innermost) has body = ctr
      // Each outer lambda has body = the lambda inside it
      Term body = ctr;
      for (int32_t i = ari - 1; i >= 0; i--) {
        HEAP[lam_locs[i]] = body;
        body = new_term(0, LAM, 0, lam_locs[i]);
      }
      Term template = body;

      return inject(template, collapsed, ari);
    }

    default: {
      return term;
    }
  }
}
