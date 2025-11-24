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
static u64 ITRS = 0;

static int DEBUG = 0;

// System Helpers
// ==============

static void error(const char *msg) {
  fprintf(stderr, "ERROR: %s\n", msg);
  exit(1);
}

static void path_join(char *out, int size, const char *base, const char *rel) {
  if (rel[0] == '/') {
    snprintf(out, size, "%s", rel);
    return;
  }
  const char *slash = strrchr(base, '/');
  if (slash) {
    int dir_len = (int)(slash - base);
    snprintf(out, size, "%.*s/%s", dir_len, base, rel);
  } else {
    snprintf(out, size, "%s", rel);
  }
}

static char *file_read(const char *path) {
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

static inline Term new_term(u8 sub, u8 tag, u32 ext, u32 val) {
  return ((u64)sub << SUB_SHIFT)
       | ((u64)(tag & TAG_MASK) << TAG_SHIFT)
       | ((u64)(ext & EXT_MASK) << EXT_SHIFT)
       | ((u64)(val & VAL_MASK));
}

static inline u8 sub_of(Term t) {
  return (t >> SUB_SHIFT) & SUB_MASK;
}

static inline u8 tag_of(Term t) {
  return (t >> TAG_SHIFT) & TAG_MASK;
}

static inline u32 ext_of(Term t) {
  return (t >> EXT_SHIFT) & EXT_MASK;
}

static inline u32 val_of(Term t) {
  return (t >> VAL_SHIFT) & VAL_MASK;
}

static inline Term mark_sub(Term t) {
  return t | ((u64)1 << SUB_SHIFT);
}

static inline Term clear_sub(Term t) {
  return t & ~(((u64)SUB_MASK) << SUB_SHIFT);
}

static inline u64 heap_alloc(u64 size) {
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

static int char_to_b64(char c) {
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

static int is_name_start(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

static int is_name_char(char c) {
  return char_to_b64(c) >= 0;
}

// Term Constructors
// =================

static inline Term New(u8 tag, u32 ext, u32 arity, Term *args) {
  u64 loc = heap_alloc(arity);
  for (u32 i = 0; i < arity; i++) {
    HEAP[loc+i] = args[i];
  }
  return new_term(0, tag, ext, loc);
}

static inline Term Var(u32 loc) {
  return new_term(0, VAR, 0, loc);
}

static inline Term Ref(u32 name) {
  return new_term(0, REF, name, 0);
}

static inline Term Nam(u32 name) {
  return new_term(0, NAM, 0, name);
}

static inline Term Era(void) {
  return new_term(0, ERA, 0, 0);
}

static inline Term Co0(u32 label, u32 loc) {
  return new_term(0, CO0, label, loc);
}

static inline Term Co1(u32 label, u32 loc) {
  return new_term(0, CO1, label, loc);
}

static inline Term Lam(Term body) {
  return New(LAM, 0, 1, (Term[]){body});
}

static inline Term App(Term fun, Term arg) {
  return New(APP, 0, 2, (Term[]){fun, arg});
}

static inline Term Sup(u32 label, Term tm0, Term tm1) {
  return New(SUP, label, 2, (Term[]){tm0, tm1});
}

static inline Term Dry(Term tm0, Term tm1) {
  return New(DRY, 0, 2, (Term[]){tm0, tm1});
}

static inline Term Dup(u32 label, Term val, Term body) {
  return New(DUP, label, 2, (Term[]){val, body});
}

static inline Term Mat(u32 name, Term val, Term next) {
  return New(MAT, name, 2, (Term[]){val, next});
}

static inline Term Ctr(u32 name, u32 arity, Term *args) {
  return New(CT0 + arity, name, arity, args);
}

// Stringifier
// ===========

static void print_name(u32 n) {
  if (n < 64) {
    putchar(alphabet[n]);
  } else {
    print_name(n / 64);
    putchar(alphabet[n % 64]);
  }
}

static void print_term_go(Term term, u32 depth);

static void print_term_go(Term term, u32 depth) {
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
      u32 name = depth + 1;
      printf("λ");
      print_name(name);
      printf(".");
      print_term_go(HEAP[loc], depth + 1);
      break;
    }
    case APP:
    case DRY: {
      Term spine[256];
      u32 len = 0;
      Term curr = term;
      while ((tag_of(curr) == APP || tag_of(curr) == DRY) && len < 256) {
        u32 loc = val_of(curr);
        spine[len++] = HEAP[loc+1];
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
      print_term_go(HEAP[loc], depth);
      printf(",");
      print_term_go(HEAP[loc+1], depth);
      printf("}");
      break;
    }
    case DUP: {
      u32 loc = val_of(term);
      u32 name = depth + 1;
      printf("!");
      print_name(name);
      printf("&");
      print_name(ext_of(term));
      printf("=");
      print_term_go(HEAP[loc], depth);
      printf(";");
      print_term_go(HEAP[loc+1], depth + 1);
      break;
    }
    case MAT: {
      u32 loc = val_of(term);
      printf("λ{#");
      print_name(ext_of(term));
      printf(":");
      print_term_go(HEAP[loc], depth);
      printf(";");
      print_term_go(HEAP[loc+1], depth);
      printf("}");
      break;
    }
    case CT0 ... CTG: {
      u32 arity = tag_of(term) - CT0;
      u32 loc = val_of(term);
      printf("#");
      print_name(ext_of(term));
      printf("{");
      for (u32 i = 0; i < arity; i++) {
        if (i > 0) {
          printf(",");
        }
        print_term_go(HEAP[loc+i], depth);
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

static void print_term(Term term) {
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

static void parse_error(PState *s, const char *expected, char detected) {
  fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m (%s:%d:%d)\n", s->file, s->line, s->col);
  fprintf(stderr, "- expected: %s\n", expected);
  if (detected == 0) {
    fprintf(stderr, "- detected: EOF\n");
  } else {
    fprintf(stderr, "- detected: '%c'\n", detected);
  }
  exit(1);
}

static inline int at_end(PState *s) {
  return s->pos >= s->len;
}

static inline char peek_at(PState *s, u32 offset) {
  u32 idx = s->pos + offset;
  if (idx >= s->len) {
    return 0;
  }
  return s->src[idx];
}

static inline char peek(PState *s) {
  return peek_at(s, 0);
}

static inline void advance(PState *s) {
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

static int starts_with(PState *s, const char *str) {
  u32 i = 0;
  while (str[i]) {
    if (peek_at(s, i) != str[i]) {
      return 0;
    }
    i++;
  }
  return 1;
}

static int match(PState *s, const char *str) {
  if (!starts_with(s, str)) {
    return 0;
  }
  while (*str) {
    advance(s);
    str++;
  }
  return 1;
}

static int is_space(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

static void skip_comment(PState *s) {
  while (!at_end(s) && peek(s) != '\n') {
    advance(s);
  }
}

static void skip(PState *s) {
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

static void consume(PState *s, const char *str) {
  skip(s);
  if (!match(s, str)) {
    parse_error(s, str, peek(s));
  }
  skip(s);
}

static void bind_push(u32 name, u32 depth) {
  PARSE_BINDS[PARSE_BINDS_LEN++] = (PBind){name, depth};
}

static void bind_pop(void) {
  PARSE_BINDS_LEN--;
}

static int bind_lookup(u32 name, u32 depth) {
  for (int i = PARSE_BINDS_LEN - 1; i >= 0; i--) {
    if (PARSE_BINDS[i].name == name) {
      return depth - 1 - PARSE_BINDS[i].depth;
    }
  }
  return -1;
}

static u32 parse_name(PState *s) {
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

static Term parse_term(PState *s, u32 depth);
static void parse_def(PState *s);

static Term parse_mat_body(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '}') {
    consume(s, "}");
    return Era();
  }
  if (peek(s) == '#') {
    consume(s, "#");
    u32 name = parse_name(s);
    consume(s, ":");
    Term val = parse_term(s, depth);
    skip(s);
    match(s, ";");
    skip(s);
    Term nxt = parse_mat_body(s, depth);
    return Mat(name, val, nxt);
  }
  Term val = parse_term(s, depth);
  consume(s, "}");
  return val;
}

static Term parse_lam(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '{') {
    consume(s, "{");
    return parse_mat_body(s, depth);
  }
  u32 name = parse_name(s);
  consume(s, ".");
  bind_push(name, depth);
  u64 loc = heap_alloc(1);
  Term body = parse_term(s, depth + 1);
  HEAP[loc] = body;
  bind_pop();
  // Store bruijn index in ext field for book terms
  return new_term(0, LAM, depth, loc);
}

static Term parse_dup(PState *s, u32 depth) {
  u32 name = parse_name(s);
  consume(s, "&");
  u32 label = parse_name(s);
  consume(s, "=");
  Term val = parse_term(s, depth);
  skip(s);
  match(s, ";");
  skip(s);
  bind_push(name, depth);
  u64 loc = heap_alloc(2);
  HEAP[loc] = val;
  Term body = parse_term(s, depth + 1);
  HEAP[loc+1] = body;
  bind_pop();
  // Store label in ext field
  return new_term(0, DUP, label, loc);
}

static Term parse_sup(PState *s, u32 depth) {
  skip(s);
  if (peek(s) == '{') {
    consume(s, "{");
    consume(s, "}");
    return Era();
  }
  u32 label = parse_name(s);
  consume(s, "{");
  Term tm0 = parse_term(s, depth);
  skip(s);
  match(s, ",");
  skip(s);
  Term tm1 = parse_term(s, depth);
  consume(s, "}");
  return Sup(label, tm0, tm1);
}

static Term parse_ctr(PState *s, u32 depth) {
  u32 name = parse_name(s);
  consume(s, "{");
  Term args[16];
  u32 cnt = 0;
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
  return Ctr(name, cnt, args);
}

static Term parse_ref(PState *s) {
  skip(s);
  if (peek(s) == '{') {
    parse_error(s, "reference name", peek(s));
  }
  u32 name = parse_name(s);
  return Ref(name);
}

static Term parse_par(PState *s, u32 depth) {
  Term term = parse_term(s, depth);
  consume(s, ")");
  return term;
}

static Term parse_var(PState *s, u32 depth) {
  skip(s);
  u32 name = parse_name(s);
  int idx = bind_lookup(name, depth);
  skip(s);
  int side = -1;
  if (match(s, "₀")) {
    side = 0;
  } else if (match(s, "₁")) {
    side = 1;
  }
  skip(s);
  // Store bruijn index in val field
  u32 val = (idx >= 0) ? (u32)idx : name;
  if (side == 0) {
    return new_term(0, CO0, 0, val);
  }
  if (side == 1) {
    return new_term(0, CO1, 0, val);
  }
  return new_term(0, VAR, 0, val);
}

static Term parse_app(Term f, PState *s, u32 depth) {
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

static Term parse_term(PState *s, u32 depth) {
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

static void do_include(PState *s, const char *filename) {
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
    .src = src,
    .pos = 0,
    .len = strlen(src),
    .line = 1,
    .col = 1
  };
  parse_def(&sub);
  free(src);
}

static void parse_include(PState *s) {
  skip(s);
  consume(s, "\"");
  u32 start = s->pos;
  while (peek(s) != '"' && !at_end(s)) {
    advance(s);
  }
  u32 end = s->pos;
  consume(s, "\"");
  char *filename = malloc(end - start + 1);
  memcpy(filename, s->src + start, end - start);
  filename[end - start] = 0;
  do_include(s, filename);
  free(filename);
}

static void parse_def(PState *s) {
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
    u32 name = parse_name(s) & EXT_MASK;
    consume(s, "=");
    PARSE_BINDS_LEN = 0;
    Term val = parse_term(s, 0);
    u64 loc = heap_alloc(1);
    HEAP[loc] = val;
    BOOK[name] = (u32)loc;
    parse_def(s);
    return;
  }
  parse_error(s, "definition or #include", peek(s));
}

// Cloning
// =======

static void clone(u32 label, Term val, Term *out0, Term *out1) {
  u64 loc = heap_alloc(1);
  HEAP[loc] = val;
  *out0 = new_term(0, CO0, label, loc);
  *out1 = new_term(0, CO1, label, loc);
}

// Beta Interactions
// =================

static Term app_era(Term era, Term arg) {
  ITRS++;
  return Era();
}

static Term app_nam(Term nam, Term arg) {
  ITRS++;
  return Dry(nam, arg);
}

static Term app_dry(Term dry, Term arg) {
  ITRS++;
  return Dry(dry, arg);
}

static Term app_lam(Term lam, Term arg) {
  ITRS++;
  u32 loc = val_of(lam);
  Term body = HEAP[loc];
  HEAP[loc] = mark_sub(arg);
  return body;
}

static Term app_sup(Term sup, Term arg) {
  ITRS++;
  u32 label = ext_of(sup);
  u32 loc = val_of(sup);
  Term tm0 = HEAP[loc+0];
  Term tm1 = HEAP[loc+1];
  Term arg0, arg1;
  clone(label, arg, &arg0, &arg1);
  return Sup(label, App(tm0, arg0), App(tm1, arg1));
}

// Match Interactions
// ==================

static Term app_mat_era(Term mat, Term arg) {
  ITRS++;
  return Era();
}

static Term app_mat_sup(Term mat, Term sup) {
  ITRS++;
  u32 sup_label = ext_of(sup);
  Term m0, m1;
  clone(sup_label, mat, &m0, &m1);
  u32 sup_loc = val_of(sup);
  Term a = HEAP[sup_loc+0];
  Term b = HEAP[sup_loc+1];
  return Sup(sup_label, App(m0, a), App(m1, b));
}

static Term app_mat_ctr(Term mat, Term ctr) {
  ITRS++;
  u32 mat_nam = ext_of(mat);
  u32 ctr_nam = ext_of(ctr);
  u32 mat_loc = val_of(mat);
  Term val = HEAP[mat_loc+0];
  Term nxt = HEAP[mat_loc+1];
  if (mat_nam == ctr_nam) {
    u32 ctr_loc = val_of(ctr);
    u32 arity = tag_of(ctr) - CT0;
    Term res = val;
    for (u32 i = 0; i < arity; i++) {
      res = App(res, HEAP[ctr_loc+i]);
    }
    return res;
  } else {
    return App(nxt, ctr);
  }
}

// Dup Interactions
// ================

static Term dup_era(u32 label, u32 loc, u8 side, Term era) {
  ITRS++;
  HEAP[loc] = mark_sub(Era());
  return Era();
}

static Term dup_lam(u32 label, u32 loc, u8 side, Term lam) {
  ITRS++;
  u32 lam_loc = val_of(lam);
  Term body = HEAP[lam_loc];
  Term b0, b1;
  clone(label, body, &b0, &b1);
  Term lam0 = Lam(b0);
  Term lam1 = Lam(b1);
  u32 sk0 = val_of(lam0);
  u32 sk1 = val_of(lam1);
  Term sup = Sup(label, Var(sk0), Var(sk1));
  HEAP[lam_loc] = mark_sub(sup);
  if (side == 0) {
    HEAP[loc] = mark_sub(lam1);
    return lam0;
  } else {
    HEAP[loc] = mark_sub(lam0);
    return lam1;
  }
}

static Term dup_sup(u32 label, u32 loc, u8 side, Term sup) {
  ITRS++;
  u32 sup_label = ext_of(sup);
  u32 sup_loc = val_of(sup);
  Term tm0 = HEAP[sup_loc+0];
  Term tm1 = HEAP[sup_loc+1];
  if (label == sup_label) {
    if (side == 0) {
      HEAP[loc] = mark_sub(tm1);
      return tm0;
    } else {
      HEAP[loc] = mark_sub(tm0);
      return tm1;
    }
  } else {
    Term a0, a1, b0, b1;
    clone(label, tm0, &a0, &a1);
    clone(label, tm1, &b0, &b1);
    Term res0 = Sup(sup_label, a0, b0);
    Term res1 = Sup(sup_label, a1, b1);
    if (side == 0) {
      HEAP[loc] = mark_sub(res1);
      return res0;
    } else {
      HEAP[loc] = mark_sub(res0);
      return res1;
    }
  }
}

static Term dup_ctr(u32 label, u32 loc, u8 side, Term ctr) {
  ITRS++;
  u32 arity = tag_of(ctr) - CT0;
  u32 ctr_nam = ext_of(ctr);
  u32 ctr_loc = val_of(ctr);
  Term args0[16], args1[16];
  for (u32 i = 0; i < arity; i++) {
    clone(label, HEAP[ctr_loc+i], &args0[i], &args1[i]);
  }
  Term res0 = Ctr(ctr_nam, arity, args0);
  Term res1 = Ctr(ctr_nam, arity, args1);
  if (side == 0) {
    HEAP[loc] = mark_sub(res1);
    return res0;
  } else {
    HEAP[loc] = mark_sub(res0);
    return res1;
  }
}

static Term dup_mat(u32 label, u32 loc, u8 side, Term mat) {
  ITRS++;
  u32 mat_nam = ext_of(mat);
  u32 mat_loc = val_of(mat);
  Term val = HEAP[mat_loc+0];
  Term nxt = HEAP[mat_loc+1];
  Term v0, v1, n0, n1;
  clone(label, val, &v0, &v1);
  clone(label, nxt, &n0, &n1);
  Term res0 = Mat(mat_nam, v0, n0);
  Term res1 = Mat(mat_nam, v1, n1);
  if (side == 0) {
    HEAP[loc] = mark_sub(res1);
    return res0;
  } else {
    HEAP[loc] = mark_sub(res0);
    return res1;
  }
}

static Term dup_nam(u32 label, u32 loc, u8 side, Term nam) {
  ITRS++;
  HEAP[loc] = mark_sub(nam);
  return nam;
}

static Term dup_dry(u32 label, u32 loc, u8 side, Term dry) {
  ITRS++;
  u32 dry_loc = val_of(dry);
  Term tm0 = HEAP[dry_loc+0];
  Term tm1 = HEAP[dry_loc+1];
  Term a0, a1, b0, b1;
  clone(label, tm0, &a0, &a1);
  clone(label, tm1, &b0, &b1);
  Term res0 = Dry(a0, b0);
  Term res1 = Dry(a1, b1);
  if (side == 0) {
    HEAP[loc] = mark_sub(res1);
    return res0;
  } else {
    HEAP[loc] = mark_sub(res0);
    return res1;
  }
}

// Alloc Interactions
// ==================

static Term alo_var(u32 ls_loc, u32 idx) {
  u32 cur = ls_loc;
  for (u32 i = 0; i < idx && cur != 0; i++) {
    u64 node = HEAP[cur];
    cur = (u32)(node >> 32);
  }
  if (cur != 0) {
    u64 node = HEAP[cur];
    u32 bind = (u32)(node & 0xFFFFFFFF);
    return Var(bind);
  }
  return new_term(0, VAR, 0, idx);
}

static Term alo_co0(u32 ls_loc, u32 label, u32 idx) {
  u32 cur = ls_loc;
  for (u32 i = 0; i < idx && cur != 0; i++) {
    u64 node = HEAP[cur];
    cur = (u32)(node >> 32);
  }
  if (cur != 0) {
    u64 node = HEAP[cur];
    u32 bind = (u32)(node & 0xFFFFFFFF);
    return Co0(label, bind);
  }
  return new_term(0, CO0, label, idx);
}

static Term alo_co1(u32 ls_loc, u32 label, u32 idx) {
  u32 cur = ls_loc;
  for (u32 i = 0; i < idx && cur != 0; i++) {
    u64 node = HEAP[cur];
    cur = (u32)(node >> 32);
  }
  if (cur != 0) {
    u64 node = HEAP[cur];
    u32 bind = (u32)(node & 0xFFFFFFFF);
    return Co1(label, bind);
  }
  return new_term(0, CO1, label, idx);
}

static Term alo_lam(u32 ls_loc, u32 book_body_loc) {
  u64 new_lam_body_loc = heap_alloc(1);
  u64 new_bind = heap_alloc(1);
  HEAP[new_bind] = ((u64)ls_loc << 32) | (u32)new_lam_body_loc;
  u64 new_alo = heap_alloc(1);
  HEAP[new_alo] = ((u64)new_bind << 32) | book_body_loc;
  HEAP[new_lam_body_loc] = new_term(0, ALO, 0, new_alo);
  return new_term(0, LAM, 0, new_lam_body_loc);
}

static Term alo_app(u32 ls_loc, u32 app_loc) {
  u64 alo_f = heap_alloc(1);
  u64 alo_x = heap_alloc(1);
  HEAP[alo_f] = ((u64)ls_loc << 32) | app_loc;
  HEAP[alo_x] = ((u64)ls_loc << 32) | (app_loc + 1);
  return App(new_term(0, ALO, 0, alo_f), new_term(0, ALO, 0, alo_x));
}

static Term alo_dup(u32 ls_loc, u32 book_dup_loc, u32 book_label) {
  u64 new_dup_val_loc = heap_alloc(1);
  u64 new_bind = heap_alloc(1);
  HEAP[new_bind] = ((u64)ls_loc << 32) | (u32)new_dup_val_loc;
  u64 alo_val = heap_alloc(1);
  HEAP[alo_val] = ((u64)ls_loc << 32) | book_dup_loc;
  HEAP[new_dup_val_loc] = new_term(0, ALO, 0, alo_val);
  u64 alo_body = heap_alloc(1);
  HEAP[alo_body] = ((u64)new_bind << 32) | (book_dup_loc + 1);
  return Dup(book_label, new_term(0, ALO, 0, alo_val), new_term(0, ALO, 0, alo_body));
}

static Term alo_sup(u32 ls_loc, u32 sup_loc, u32 sup_label) {
  u64 alo_a = heap_alloc(1);
  u64 alo_b = heap_alloc(1);
  HEAP[alo_a] = ((u64)ls_loc << 32) | sup_loc;
  HEAP[alo_b] = ((u64)ls_loc << 32) | (sup_loc + 1);
  return Sup(sup_label, new_term(0, ALO, 0, alo_a), new_term(0, ALO, 0, alo_b));
}

static Term alo_mat(u32 ls_loc, u32 mat_loc, u32 mat_nam) {
  u64 alo_h = heap_alloc(1);
  u64 alo_m = heap_alloc(1);
  HEAP[alo_h] = ((u64)ls_loc << 32) | mat_loc;
  HEAP[alo_m] = ((u64)ls_loc << 32) | (mat_loc + 1);
  return Mat(mat_nam, new_term(0, ALO, 0, alo_h), new_term(0, ALO, 0, alo_m));
}

static Term alo_ctr(u32 ls_loc, u32 ctr_loc, u32 ctr_nam, u32 arity) {
  Term args[16];
  for (u32 i = 0; i < arity; i++) {
    u64 alo_arg = heap_alloc(1);
    HEAP[alo_arg] = ((u64)ls_loc << 32) | (ctr_loc + i);
    args[i] = new_term(0, ALO, 0, alo_arg);
  }
  return Ctr(ctr_nam, arity, args);
}

static Term alo_dry(u32 ls_loc, u32 dry_loc) {
  u64 alo_f = heap_alloc(1);
  u64 alo_x = heap_alloc(1);
  HEAP[alo_f] = ((u64)ls_loc << 32) | dry_loc;
  HEAP[alo_x] = ((u64)ls_loc << 32) | (dry_loc + 1);
  return Dry(new_term(0, ALO, 0, alo_f), new_term(0, ALO, 0, alo_x));
}

// WNF
// ===

static Term wnf(Term term) {
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
        u32 loc = val_of(next);
        Term fun = HEAP[loc];
        STACK[S_POS++] = next;
        next = fun;
        goto enter;
      }

      case DUP: {
        u32 loc = val_of(next);
        Term body = HEAP[loc+1];
        next = body;
        goto enter;
      }

      case REF: {
        u32 name = ext_of(next);
        if (BOOK[name] != 0) {
          u64 alo_loc = heap_alloc(1);
          HEAP[alo_loc] = ((u64)0 << 32) | BOOK[name];
          next = new_term(0, ALO, 0, alo_loc);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case ALO: {
        u32 alo_loc = val_of(next);
        u64 pair = HEAP[alo_loc];
        u32 tm_loc = (u32)(pair & 0xFFFFFFFF);
        u32 ls_loc = (u32)(pair >> 32);
        Term book_term = HEAP[tm_loc];

        switch (tag_of(book_term)) {
          case VAR: {
            u32 idx = val_of(book_term);
            next = alo_var(ls_loc, idx);
            goto enter;
          }
          case CO0: {
            u32 idx = val_of(book_term);
            u32 label = ext_of(book_term);
            next = alo_co0(ls_loc, label, idx);
            goto enter;
          }
          case CO1: {
            u32 idx = val_of(book_term);
            u32 label = ext_of(book_term);
            next = alo_co1(ls_loc, label, idx);
            goto enter;
          }
          case LAM: {
            u32 book_body_loc = val_of(book_term);
            next = alo_lam(ls_loc, book_body_loc);
            goto enter;
          }
          case APP: {
            u32 app_loc = val_of(book_term);
            next = alo_app(ls_loc, app_loc);
            goto enter;
          }
          case DUP: {
            u32 book_dup_loc = val_of(book_term);
            u32 book_label = ext_of(book_term);
            next = alo_dup(ls_loc, book_dup_loc, book_label);
            goto enter;
          }
          case SUP: {
            u32 sup_loc = val_of(book_term);
            u32 sup_label = ext_of(book_term);
            next = alo_sup(ls_loc, sup_loc, sup_label);
            goto enter;
          }
          case MAT: {
            u32 mat_loc = val_of(book_term);
            u32 mat_nam = ext_of(book_term);
            next = alo_mat(ls_loc, mat_loc, mat_nam);
            goto enter;
          }
          case CT0 ... CTG: {
            u32 arity = tag_of(book_term) - CT0;
            u32 ctr_loc = val_of(book_term);
            u32 ctr_nam = ext_of(book_term);
            next = alo_ctr(ls_loc, ctr_loc, ctr_nam, arity);
            goto enter;
          }
          case REF: {
            next = book_term;
            goto enter;
          }
          case ERA: {
            whnf = Era();
            goto apply;
          }
          case NAM: {
            whnf = book_term;
            goto apply;
          }
          case DRY: {
            u32 dry_loc = val_of(book_term);
            next = alo_dry(ls_loc, dry_loc);
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
      case CT0:
      case CT1:
      case CT2:
      case CT3:
      case CT4:
      case CT5:
      case CT6:
      case CT7:
      case CT8:
      case CT9:
      case CTA:
      case CTB:
      case CTC:
      case CTD:
      case CTE:
      case CTF:
      case CTG: {
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
          u32 loc = val_of(frame);
          Term arg = HEAP[loc+1];

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
          u8 side = (tag_of(frame) == CO0) ? 0 : 1;
          u32 loc = val_of(frame);
          u32 label = ext_of(frame);

          switch (tag_of(whnf)) {
            case ERA: {
              whnf = dup_era(label, loc, side, whnf);
              continue;
            }
            case LAM: {
              whnf = dup_lam(label, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case SUP: {
              whnf = dup_sup(label, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case CT0 ... CTG: {
              whnf = dup_ctr(label, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case MAT: {
              whnf = dup_mat(label, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case NAM: {
              whnf = dup_nam(label, loc, side, whnf);
              continue;
            }
            case DRY: {
              whnf = dup_dry(label, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              u64 new_loc = heap_alloc(1);
              HEAP[new_loc] = whnf;
              HEAP[loc] = mark_sub(new_term(0, side == 1 ? CO0 : CO1, label, new_loc));
              whnf = new_term(0, side == 0 ? CO0 : CO1, label, new_loc);
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

static Term snf(Term term, u32 depth) {
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
      u64 loc = val_of(term);
      Term body = HEAP[loc];
      HEAP[loc] = mark_sub(Nam(depth + 1));
      body = snf(body, depth + 1);
      HEAP[loc] = body;
      return term;
    }
    case APP: {
      u64 loc = val_of(term);
      HEAP[loc] = snf(HEAP[loc], depth);
      HEAP[loc+1] = snf(HEAP[loc+1], depth);
      return term;
    }
    case MAT: {
      u64 loc = val_of(term);
      HEAP[loc] = snf(HEAP[loc], depth);
      HEAP[loc+1] = snf(HEAP[loc+1], depth);
      return term;
    }
    case SUP: {
      u64 loc = val_of(term);
      HEAP[loc] = snf(HEAP[loc], depth);
      HEAP[loc+1] = snf(HEAP[loc+1], depth);
      return term;
    }
    case DRY: {
      u64 loc = val_of(term);
      HEAP[loc] = snf(HEAP[loc], depth);
      HEAP[loc+1] = snf(HEAP[loc+1], depth);
      return term;
    }
    case DUP: {
      printf("TODO\n");
      abort();
    }
    case CT0 ... CTG: {
      u32 arity = tag_of(term) - CT0;
      u64 loc = val_of(term);
      for (u32 i = 0; i < arity; i++) {
        HEAP[loc+i] = snf(HEAP[loc+i], depth);
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
    .src = (char*)source,
    .pos = 0,
    .len = strlen(source),
    .line = 1,
    .col = 1
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
  Term result = snf(main_term, 0);
  clock_t end = clock();

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
