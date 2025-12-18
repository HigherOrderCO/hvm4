// Global state for pretty printing with globally unique names
// ===========================================================

// Maps from heap location to assigned name
static u32  PRINT_LAM_LOCS[65536];
static u32  PRINT_LAM_NAMES[65536];
static u32  PRINT_LAM_COUNT = 0;

static u32  PRINT_DUP_LOCS[65536];
static u32  PRINT_DUP_LABS[65536];
static u32  PRINT_DUP_NAMES[65536];
static u32  PRINT_DUP_COUNT = 0;

// Queue of discovered dup locations to print
static u32  PRINT_DUP_QUEUE[65536];
static u32  PRINT_DUP_QUEUE_LEN = 0;

// Fresh name counters (0-indexed sequence numbers)
static u32  PRINT_LAM_FRESH = 0;
static u32  PRINT_DUP_FRESH = 0;

// ALO substitution state (for book mode printing)
static u32  PRINT_ALO_BINDS[256];
static u32  PRINT_ALO_LEN = 0;

// Convert sequence number to nick value for lowercase (a, b, ..., z, aa, ab, ...)
fn u32 print_lam_nick(u32 seq) {
  if (seq < 26) {
    return seq + 1;  // a=1, b=2, ..., z=26
  }
  seq -= 26;
  u32 lo = (seq % 26) + 1;  // a=1, ..., z=26
  u32 hi = (seq / 26) + 1;  // a=1, ..., z=26, then aa, ab, ...
  return hi * 64 + lo;
}

// Convert sequence number to nick value for uppercase (A, B, ..., Z, AA, AB, ...)
fn u32 print_dup_nick(u32 seq) {
  if (seq < 26) {
    return seq + 27;  // A=27, B=28, ..., Z=52
  }
  seq -= 26;
  u32 lo = (seq % 26) + 27;  // A=27, ..., Z=52
  u32 hi = (seq / 26) + 27;  // A=27, ..., Z=52, then AA, AB, ...
  return hi * 64 + lo;
}

// Reset print state before printing a new term
fn void print_reset() {
  PRINT_LAM_COUNT     = 0;
  PRINT_DUP_COUNT     = 0;
  PRINT_DUP_QUEUE_LEN = 0;
  PRINT_LAM_FRESH     = 0;
  PRINT_DUP_FRESH     = 0;
  PRINT_ALO_LEN       = 0;
}

// Get or assign a lowercase name for a lambda/var pair (keyed by body location)
fn u32 print_get_lam_name(u32 loc) {
  for (u32 i = 0; i < PRINT_LAM_COUNT; i++) {
    if (PRINT_LAM_LOCS[i] == loc) {
      return PRINT_LAM_NAMES[i];
    }
  }
  u32 name = print_lam_nick(PRINT_LAM_FRESH++);
  PRINT_LAM_LOCS[PRINT_LAM_COUNT]  = loc;
  PRINT_LAM_NAMES[PRINT_LAM_COUNT] = name;
  PRINT_LAM_COUNT++;
  return name;
}

// Get or assign an uppercase name for a dup (keyed by location)
// Also queues the dup for printing if newly discovered
fn u32 print_get_dup_name(u32 loc, u32 lab) {
  for (u32 i = 0; i < PRINT_DUP_COUNT; i++) {
    if (PRINT_DUP_LOCS[i] == loc) {
      return PRINT_DUP_NAMES[i];
    }
  }
  // New dup discovered - assign name and queue for printing
  u32 name = print_dup_nick(PRINT_DUP_FRESH++);
  PRINT_DUP_LOCS[PRINT_DUP_COUNT]  = loc;
  PRINT_DUP_LABS[PRINT_DUP_COUNT]  = lab;
  PRINT_DUP_NAMES[PRINT_DUP_COUNT] = name;
  PRINT_DUP_COUNT++;
  PRINT_DUP_QUEUE[PRINT_DUP_QUEUE_LEN++] = PRINT_DUP_COUNT - 1;
  return name;
}

// Forward declarations
fn void print_term_go(FILE *f, Term term, u32 depth, int book);
fn void print_ctr(FILE *f, Term t, u32 d, int book);

fn void print_mat_name(FILE *f, u32 nam) {
  if (nam == NAM_ZER) {
    fputs("0n", f);
  } else if (nam == NAM_SUC) {
    fputs("1n+", f);
  } else if (nam == NAM_NIL) {
    fputs("[]", f);
  } else if (nam == NAM_CON) {
    fputs("<>", f);
  } else {
    fputc('#', f);
    print_name(f, nam);
  }
}

// Prints APP and DRY chains as f(x,y,z)
fn void print_app(FILE *f, Term term, u32 depth, int book) {
  Term spine[256];
  u32  len  = 0;
  Term curr = term;
  while ((term_tag(curr) == APP || term_tag(curr) == DRY) && len < 256) {
    u32 loc = term_val(curr);
    spine[len++] = HEAP[loc + 1];
    curr = HEAP[loc];
  }
  if (term_tag(curr) == LAM) {
    fputc('(', f);
    print_term_go(f, curr, depth, book);
    fputc(')', f);
  } else {
    print_term_go(f, curr, depth, book);
  }
  fputc('(', f);
  for (u32 i = 0; i < len; i++) {
    if (i > 0) {
      fputc(',', f);
    }
    print_term_go(f, spine[len - 1 - i], depth, book);
  }
  fputc(')', f);
}

fn void print_term_go(FILE *f, Term term, u32 depth, int book) {
  switch (term_tag(term)) {
    case NAM: {
      // Print stuck variable as just the name
      print_name(f, term_ext(term));
      break;
    }
    case DRY: {
      // Print stuck application as f(x,y)
      print_app(f, term, depth, book);
      break;
    }
    case VAR: {
      if (book) {
        // Book mode: val is de Bruijn index, substitute from ALO bindings
        u32 idx = term_val(term);
        if (idx < PRINT_ALO_LEN) {
          u32 bind = PRINT_ALO_BINDS[idx];
          // Get value - SUB slot contains the term directly (just unmark it)
          Term val = HEAP[bind];
          while (term_sub(val)) {
            val = term_unmark(val);
          }
          print_term_go(f, val, depth, 0);  // Print in runtime mode
        } else {
          fprintf(f, "^%u", idx);  // Fallback for unbound
        }
      } else {
        // Runtime mode: val is heap location
        u32 loc = term_val(term);
        u32 nam = print_get_lam_name(loc);
        print_name(f, nam);
      }
      break;
    }
    case NUM: {
      fprintf(f, "%u", term_val(term));
      break;
    }
    case REF: {
      fputc('@', f);
      char *name = table_get(term_ext(term));
      if (name != NULL) {
        fputs(name, f);
      } else {
        print_name(f, term_ext(term));
      }
      break;
    }
    case ERA: {
      fputs("&{}", f);
      break;
    }
    case ANY: {
      fputc('*', f);
      break;
    }
    case CO0:
    case CO1: {
      u32 loc = term_val(term);
      u32 lab = term_ext(term);
      if (book) {
        // Book mode: val is de Bruijn index, substitute from ALO bindings
        u32 idx = loc;
        if (idx < PRINT_ALO_LEN) {
          u32 bind = PRINT_ALO_BINDS[idx];
          // Get value - SUB slot contains the term directly (just unmark it)
          Term val = HEAP[bind];
          while (term_sub(val)) {
            val = term_unmark(val);
          }
          print_term_go(f, val, depth, 0);  // Print substituted value (no subscript)
        } else {
          fprintf(f, "^%u", idx);  // Fallback for unbound
          fputs(term_tag(term) == CO0 ? "\xe2\x82\x80" : "\xe2\x82\x81", f);
        }
      } else {
        // Runtime mode: val is heap location
        // Follow substitutions to find canonical location
        Term val = HEAP[loc];
        while (term_sub(val)) {
          val = term_unmark(val);  // SUB slot contains term directly
          // If substituted to another CO, follow to its dup location
          if (term_tag(val) == CO0 || term_tag(val) == CO1) {
            loc = term_val(val);
            val = HEAP[loc];
          } else {
            break;
          }
        }
        u32 nam = print_get_dup_name(loc, lab);
        print_name(f, nam);
        fputs(term_tag(term) == CO0 ? "\xe2\x82\x80" : "\xe2\x82\x81", f);
      }
      break;
    }
    case LAM: {
      u32 loc = term_val(term);
      fputs("\xce\xbb", f);
      if (book) {
        // Book mode: ext is bru_depth, use it for naming
        print_name(f, print_lam_nick(term_ext(term)));
      } else {
        // Runtime mode: use location for naming
        u32 nam = print_get_lam_name(loc);
        print_name(f, nam);
      }
      fputc('.', f);
      print_term_go(f, HEAP[loc], depth + 1, book);
      break;
    }
    case APP: {
      print_app(f, term, depth, book);
      break;
    }
    case SUP: {
      u32 loc = term_val(term);
      fputc('&', f);
      print_name(f, term_ext(term));
      fputc('{', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputc(',', f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc('}', f);
      break;
    }
    case DUP: {
      u32 loc = term_val(term);
      u32 lab = term_ext(term);
      if (book) {
        // Book mode: print with label, use depth for naming
        fputc('!', f);
        print_name(f, print_dup_nick(term_ext(term)));
        fputc('&', f);
        print_name(f, lab);
        fputc('=', f);
        print_term_go(f, HEAP[loc + 0], depth, book);
        fputc(';', f);
        print_term_go(f, HEAP[loc + 1], depth + 1, book);
      } else {
        // Runtime mode: use location for naming
        u32 nam = print_get_dup_name(loc, lab);
        fputc('!', f);
        print_name(f, nam);
        fputc('&', f);
        print_name(f, lab);
        fputc('=', f);
        print_term_go(f, HEAP[loc + 0], depth, book);
        fputc(';', f);
        print_term_go(f, HEAP[loc + 1], depth + 1, book);
      }
      break;
    }
    case MAT:
    case SWI: {
      fputs("\xce\xbb{", f);
      Term cur = term;
      while (term_tag(cur) == MAT || term_tag(cur) == SWI) {
        u32 loc = term_val(cur);
        if (term_tag(cur) == SWI) {
          fprintf(f, "%u", term_ext(cur));
        } else {
          print_mat_name(f, term_ext(cur));
        }
        fputc(':', f);
        print_term_go(f, HEAP[loc + 0], depth, book);
        Term next = HEAP[loc + 1];
        if (term_tag(next) == MAT || term_tag(next) == SWI) {
          fputc(';', f);
        }
        cur = next;
      }
      // Handle tail: NUM(0) = empty, USE = wrapped default, other = default
      if (term_tag(cur) == NUM && term_val(cur) == 0) {
        // empty default - just close
      } else if (term_tag(cur) == USE) {
        fputc(';', f);
        print_term_go(f, HEAP[term_val(cur)], depth, book);
      } else {
        fputc(';', f);
        print_term_go(f, cur, depth, book);
      }
      fputc('}', f);
      break;
    }
    case USE: {
      u32 loc = term_val(term);
      fputs("\xce\xbb{", f);
      print_term_go(f, HEAP[loc], depth, book);
      fputc('}', f);
      break;
    }
    case C00 ... C16: {
      print_ctr(f, term, depth, book);
      break;
    }
    case OP2: {
      u32 opr = term_ext(term);
      u32 loc = term_val(term);
      static const char *op_syms[] = {
        "+", "-", "*", "/", "%", "&&", "||", "^", "<<", ">>",
        "~", "==", "!=", "<", "<=", ">", ">="
      };
      fputc('(', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputc(' ', f);
      if (opr < 17) {
        fputs(op_syms[opr], f);
      } else {
        fprintf(f, "?%u", opr);
      }
      fputc(' ', f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(')', f);
      break;
    }
    case DSU: {
      u32 loc = term_val(term);
      fputs("&(", f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs("){", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(',', f);
      print_term_go(f, HEAP[loc + 2], depth, book);
      fputc('}', f);
      break;
    }
    case DDU: {
      u32 loc = term_val(term);
      fputs("!(", f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs(")=", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(';', f);
      print_term_go(f, HEAP[loc + 2], depth, book);
      break;
    }
    case ALO: {
      // ALO stores (bind_list_head << 32 | book_term_loc) at HEAP[alo_loc]
      u32 alo_loc = term_val(term);
      u64 pair    = HEAP[alo_loc];
      u32 tm_loc  = (u32)(pair & 0xFFFFFFFF);
      u32 ls_loc  = (u32)(pair >> 32);
      // Collect bindings (most recent first, index 0 = innermost)
      u32 bind_locs[256];
      u32 bind_len = 0;
      u32 ls = ls_loc;
      while (ls != 0 && bind_len < 256) {
        bind_locs[bind_len++] = (u32)(HEAP[ls] >> 32);
        ls = (u32)(HEAP[ls] & 0xFFFFFFFF);
      }
      // Set up ALO substitution state
      u32 old_len = PRINT_ALO_LEN;
      for (u32 i = 0; i < bind_len; i++) {
        PRINT_ALO_BINDS[i] = bind_locs[i];
      }
      PRINT_ALO_LEN = bind_len;
      // Print @{book_term} with substitutions applied in-place
      fputs("@{", f);
      print_term_go(f, HEAP[tm_loc], bind_len, 1);
      fputc('}', f);
      // Restore ALO state (for nested ALOs)
      PRINT_ALO_LEN = old_len;
      break;
    }
    case RED: {
      u32 loc = term_val(term);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs(" ~> ", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      break;
    }
    case EQL: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs(" === ", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(')', f);
      break;
    }
    case AND: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs(" .&. ", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(')', f);
      break;
    }
    case OR: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputs(" .|. ", f);
      print_term_go(f, HEAP[loc + 1], depth, book);
      fputc(')', f);
      break;
    }
    case UNS: {
      u32 loc = term_val(term);
      // UNS body is λf.λv.actual_body - extract names from depths
      Term lam_f = HEAP[loc];
      u32 nam_f = depth + 1;
      Term lam_v = HEAP[term_val(lam_f)];
      u32 nam_v = depth + 2;
      Term body = HEAP[term_val(lam_v)];
      fputs("! ", f);
      print_name(f, nam_f);
      fputs(" = \xce\xbb ", f);
      print_name(f, nam_v);
      fputs(" ; ", f);
      print_term_go(f, body, depth + 2, book);
      break;
    }
    case INC: {
      u32 loc = term_val(term);
      fputs("\xe2\x86\x91", f);
      print_term_go(f, HEAP[loc], depth, book);
      break;
    }
  }
}

fn void print_ctr(FILE *f, Term t, u32 d, int book) {
  u32 nam = term_ext(t), loc = term_val(t), ari = term_tag(t) - C00;
  // Nat: count SUCs, print as Nn or Nn+x
  if (nam == NAM_ZER || nam == NAM_SUC) {
    u32 n = 0;
    while (term_tag(t) == C01 && term_ext(t) == NAM_SUC) {
      n++;
      t = HEAP[term_val(t)];
    }
    fprintf(f, "%un", n);
    if (!(term_tag(t) == C00 && term_ext(t) == NAM_ZER)) {
      fputc('+', f);
      print_term_go(f, t, d, book);
    }
    return;
  }
  // Char: 'x' or 'λ'
  if (nam == NAM_CHR && ari == 1 && term_tag(HEAP[loc]) == NUM) {
    u32 c = term_val(HEAP[loc]);
    if (c >= 32 && c != 127) {
      fputc('\'', f);
      print_utf8(f, c);
      fputc('\'', f);
      return;
    }
  }
  // List/String
  if (nam == NAM_NIL || nam == NAM_CON) {
    // Check if string (non-empty, all printable chars including Unicode)
    int is_str = (nam == NAM_CON);
    for (Term x = t; term_tag(x) == C02 && term_ext(x) == NAM_CON; x = HEAP[term_val(x)+1]) {
      Term h = HEAP[term_val(x)];
      if (!(term_tag(h) == C01 && term_ext(h) == NAM_CHR)) {
        is_str = 0;
        break;
      }
      if (term_tag(HEAP[term_val(h)]) != NUM) {
        is_str = 0;
        break;
      }
      u32 c = term_val(HEAP[term_val(h)]);
      if (c < 32 || c == 127) {
        is_str = 0;
        break;
      }
    }
    Term end = t;
    while (term_tag(end) == C02 && term_ext(end) == NAM_CON) {
      end = HEAP[term_val(end)+1];
    }
    if (is_str && term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('"', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1]) {
        print_utf8(f, term_val(HEAP[term_val(HEAP[term_val(x)])]));
      }
      fputc('"', f);
      return;
    }
    // Proper list: [a,b,c]
    if (term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('[', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1]) {
        if (x != t) {
          fputc(',', f);
        }
        print_term_go(f, HEAP[term_val(x)], d, book);
      }
      fputc(']', f);
      return;
    }
    // Improper list: h<>t
    if (nam == NAM_CON) {
      print_term_go(f, HEAP[loc], d, book);
      fputs("<>", f);
      print_term_go(f, HEAP[loc+1], d, book);
      return;
    }
  }
  // Default CTR
  fputc('#', f);
  print_name(f, nam);
  fputc('{', f);
  for (u32 i = 0; i < ari; i++) {
    if (i) {
      fputc(',', f);
    }
    print_term_go(f, HEAP[loc+i], d, book);
  }
  fputc('}', f);
}

// Print a single discovered dup
fn void print_dup_at(FILE *f, u32 idx) {
  u32 loc = PRINT_DUP_LOCS[idx];
  u32 lab = PRINT_DUP_LABS[idx];
  u32 nam = PRINT_DUP_NAMES[idx];
  // Get value - SUB slot contains the term directly (just unmark it)
  Term val = HEAP[loc];
  while (term_sub(val)) {
    val = term_unmark(val);
  }
  fputs("\n! ", f);
  print_name(f, nam);
  fputs(" &", f);
  print_name(f, lab);
  fputs(" = ", f);
  print_term_go(f, val, 0, 0);
  fputc(';', f);
}

// Print all discovered dups (may discover more as we go)
fn void print_dups(FILE *f) {
  u32 printed = 0;
  while (printed < PRINT_DUP_QUEUE_LEN) {
    u32 idx = PRINT_DUP_QUEUE[printed];
    print_dup_at(f, idx);
    printed++;
  }
}

fn void print_term(Term term) {
  print_reset();
  print_term_go(stdout, term, 0, 0);
  print_dups(stdout);
}
