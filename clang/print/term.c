// Pretty Printer for HVM4 Terms
// ==============================
//
// This printer handles both runtime terms and book terms (inside ALOs).
//
// Key concepts:
// - Runtime terms use heap locations for variable/dup identity
// - Book terms use de Bruijn indices for variables
// - When printing ALOs, we substitute de Bruijn indices with runtime values
// - Lambdas and VARs share names based on body location
// - Dups and COs share names based on dup location
// - "Floating dups" are printed after the main term

// Global state for name assignment
// --------------------------------

// Lambda/VAR naming: maps body location -> assigned name
static u32  PRINT_LAM_LOCS[65536];
static u32  PRINT_LAM_NAMES[65536];
static u32  PRINT_LAM_COUNT = 0;

// Dup/CO naming: maps dup location -> assigned name
static u32  PRINT_DUP_LOCS[65536];
static u32  PRINT_DUP_LABS[65536];
static u32  PRINT_DUP_NAMES[65536];
static u32  PRINT_DUP_COUNT = 0;

// Queue of discovered dups to print as "floating dups"
static u32  PRINT_DUP_QUEUE[65536];
static u32  PRINT_DUP_QUEUE_LEN = 0;

// Fresh name counters
static u32  PRINT_LAM_FRESH = 0;
static u32  PRINT_DUP_FRESH = 0;

// ALO substitution: binding locations for de Bruijn indices
static u32  PRINT_ALO_BINDS[256];
static u32  PRINT_ALO_LEN = 0;

// Name generation
// ---------------

// Convert sequence to lowercase nick: a, b, ..., z, aa, ab, ...
fn u32 print_lam_nick(u32 seq) {
  if (seq < 26) {
    return seq + 1;  // a=1, b=2, ..., z=26
  }
  seq -= 26;
  u32 lo = (seq % 26) + 1;
  u32 hi = (seq / 26) + 1;
  return hi * 64 + lo;
}

// Convert sequence to uppercase nick: A, B, ..., Z, AA, AB, ...
fn u32 print_dup_nick(u32 seq) {
  if (seq < 26) {
    return seq + 27;  // A=27, B=28, ..., Z=52
  }
  seq -= 26;
  u32 lo = (seq % 26) + 27;
  u32 hi = (seq / 26) + 27;
  return hi * 64 + lo;
}

// Reset state before printing a new term
fn void print_reset() {
  PRINT_LAM_COUNT     = 0;
  PRINT_DUP_COUNT     = 0;
  PRINT_DUP_QUEUE_LEN = 0;
  PRINT_LAM_FRESH     = 0;
  PRINT_DUP_FRESH     = 0;
  PRINT_ALO_LEN       = 0;
}

// Get or assign lowercase name for a lambda body location
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

// Get or assign uppercase name for a dup location
// Also queues the dup for floating dup printing
fn u32 print_get_dup_name(u32 loc, u32 lab) {
  for (u32 i = 0; i < PRINT_DUP_COUNT; i++) {
    if (PRINT_DUP_LOCS[i] == loc) {
      return PRINT_DUP_NAMES[i];
    }
  }
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

// Helper for MAT case names
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

// Print APP/DRY chains as f(x,y,z)
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
    if (i > 0) fputc(',', f);
    print_term_go(f, spine[len - 1 - i], depth, book);
  }
  fputc(')', f);
}

// Main term printer
fn void print_term_go(FILE *f, Term term, u32 depth, int book) {
  switch (term_tag(term)) {

    case NAM: {
      print_name(f, term_ext(term));
      break;
    }

    case DRY: {
      print_app(f, term, depth, book);
      break;
    }

    case VAR: {
      if (book) {
        // Book mode: val is de Bruijn index
        // Substitute with the term at the corresponding binding location
        u32 idx = term_val(term);
        if (idx < PRINT_ALO_LEN) {
          u32 bind = PRINT_ALO_BINDS[idx];
          Term val = HEAP[bind];
          if (term_sub(val)) val = term_unmark(val);
          print_term_go(f, val, depth, 0);
        } else {
          fprintf(f, "^%u", idx);
        }
      } else {
        // Runtime mode: val is the lambda body location
        // If substituted, print the substituted value
        // Otherwise, print as variable name
        u32 loc = term_val(term);
        Term val = HEAP[loc];
        if (term_sub(val)) {
          print_term_go(f, term_unmark(val), depth, book);
        } else {
          print_name(f, print_get_lam_name(loc));
        }
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
        // Book mode: val is de Bruijn index
        // Substitute with the term at the corresponding binding location
        u32 idx = loc;
        if (idx < PRINT_ALO_LEN) {
          u32 bind = PRINT_ALO_BINDS[idx];
          Term val = HEAP[bind];
          if (term_sub(val)) val = term_unmark(val);
          print_term_go(f, val, depth, 0);
        } else {
          fprintf(f, "^%u", idx);
          fputs(term_tag(term) == CO0 ? "\xe2\x82\x80" : "\xe2\x82\x81", f);
        }
      } else {
        // Runtime mode: val is dup location
        // Follow CO substitution chains to find canonical location
        Term val = HEAP[loc];
        while (term_sub(val)) {
          val = term_unmark(val);
          if (term_tag(val) == CO0 || term_tag(val) == CO1) {
            loc = term_val(val);
            val = HEAP[loc];
          } else {
            break;
          }
        }
        print_name(f, print_get_dup_name(loc, lab));
        fputs(term_tag(term) == CO0 ? "\xe2\x82\x80" : "\xe2\x82\x81", f);
      }
      break;
    }

    case LAM: {
      u32 loc = term_val(term);
      fputs("\xce\xbb", f);
      if (book) {
        print_name(f, print_lam_nick(term_ext(term)));
      } else {
        print_name(f, print_get_lam_name(loc));
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
      u32 nam = book ? print_dup_nick(term_ext(term)) : print_get_dup_name(loc, lab);
      fputc('!', f);
      print_name(f, nam);
      fputs("&", f);
      print_name(f, lab);
      fputc('=', f);
      print_term_go(f, HEAP[loc + 0], depth, book);
      fputc(';', f);
      print_term_go(f, HEAP[loc + 1], depth + 1, book);
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
        if (term_tag(next) == MAT || term_tag(next) == SWI) fputc(';', f);
        cur = next;
      }
      if (term_tag(cur) == NUM && term_val(cur) == 0) {
        // empty default
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
      fputs(opr < 17 ? op_syms[opr] : "?", f);
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
      // ALO: a "quoted" book term with a substitution list
      // Structure: HEAP[alo_loc] = (list_head << 32 | book_term_loc)
      // List node: HEAP[node] = (bind_loc << 32 | next_node)
      u32 alo_loc = term_val(term);
      u64 pair    = HEAP[alo_loc];
      u32 tm_loc  = (u32)(pair & 0xFFFFFFFF);
      u32 ls_loc  = (u32)(pair >> 32);
      // Collect binding locations (index 0 = innermost/most recent)
      u32 bind_locs[256];
      u32 bind_len = 0;
      for (u32 ls = ls_loc; ls != 0 && bind_len < 256; ) {
        bind_locs[bind_len++] = (u32)(HEAP[ls] >> 32);
        ls = (u32)(HEAP[ls] & 0xFFFFFFFF);
      }
      // Set up substitution state for book mode printing
      u32 old_len = PRINT_ALO_LEN;
      for (u32 i = 0; i < bind_len; i++) {
        PRINT_ALO_BINDS[i] = bind_locs[i];
      }
      PRINT_ALO_LEN = bind_len;
      // Print book term with de Bruijn indices substituted
      fputs("@{", f);
      print_term_go(f, HEAP[tm_loc], bind_len, 1);
      fputc('}', f);
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

// Constructor printer with special cases for Nat, Char, List, String
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

  // Char: 'x'
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
    // Check if it's a printable string
    int is_str = (nam == NAM_CON);
    for (Term x = t; term_tag(x) == C02 && term_ext(x) == NAM_CON; x = HEAP[term_val(x)+1]) {
      Term h = HEAP[term_val(x)];
      if (!(term_tag(h) == C01 && term_ext(h) == NAM_CHR)) { is_str = 0; break; }
      if (term_tag(HEAP[term_val(h)]) != NUM) { is_str = 0; break; }
      u32 c = term_val(HEAP[term_val(h)]);
      if (c < 32 || c == 127) { is_str = 0; break; }
    }
    Term end = t;
    while (term_tag(end) == C02 && term_ext(end) == NAM_CON) {
      end = HEAP[term_val(end)+1];
    }
    // String: "abc"
    if (is_str && term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('"', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1]) {
        print_utf8(f, term_val(HEAP[term_val(HEAP[term_val(x)])]));
      }
      fputc('"', f);
      return;
    }
    // List: [a,b,c]
    if (term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('[', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1]) {
        if (x != t) fputc(',', f);
        print_term_go(f, HEAP[term_val(x)], d, book);
      }
      fputc(']', f);
      return;
    }
    // Cons: h<>t
    if (nam == NAM_CON) {
      print_term_go(f, HEAP[loc], d, book);
      fputs("<>", f);
      print_term_go(f, HEAP[loc+1], d, book);
      return;
    }
  }

  // Default: #Name{args}
  fputc('#', f);
  print_name(f, nam);
  fputc('{', f);
  for (u32 i = 0; i < ari; i++) {
    if (i) fputc(',', f);
    print_term_go(f, HEAP[loc+i], d, book);
  }
  fputc('}', f);
}

// Print a floating dup (discovered during main term printing)
fn void print_dup_at(FILE *f, u32 idx) {
  u32 loc = PRINT_DUP_LOCS[idx];
  u32 lab = PRINT_DUP_LABS[idx];
  u32 nam = PRINT_DUP_NAMES[idx];
  Term val = HEAP[loc];
  if (term_sub(val)) val = term_unmark(val);
  fputs("\n! ", f);
  print_name(f, nam);
  fputs(" &", f);
  print_name(f, lab);
  fputs(" = ", f);
  print_term_go(f, val, 0, 0);
  fputc(';', f);
}

// Print all floating dups (queue may grow during printing)
fn void print_dups(FILE *f) {
  for (u32 i = 0; i < PRINT_DUP_QUEUE_LEN; i++) {
    print_dup_at(f, PRINT_DUP_QUEUE[i]);
  }
}

// Main entry point
fn void print_term(Term term) {
  print_reset();
  print_term_go(stdout, term, 0, 0);
  print_dups(stdout);
}
