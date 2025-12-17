// Global naming state for print
// ==============================

#define PRINT_MAX_NAMES 65536
#define PRINT_MAX_DUPS  65536

// Maps body location -> name index for LAM/VAR (lowercase: a, b, c, ...)
static u32 print_lam_locs[PRINT_MAX_NAMES];
static u32 print_lam_names[PRINT_MAX_NAMES];
static u32 print_lam_count = 0;

// Maps dup location -> name index for DUP/CO0/CO1 (uppercase: A, B, C, ...)
static u32 print_dup_locs[PRINT_MAX_NAMES];
static u32 print_dup_names[PRINT_MAX_NAMES];
static u32 print_dup_count = 0;

// Queue of dup locations to print after main term
static u32 print_dup_queue[PRINT_MAX_DUPS];
static u32 print_dup_queue_len = 0;

// Set of already-seen dup locations (to avoid loops)
static u32 print_dup_seen[PRINT_MAX_DUPS];
static u32 print_dup_seen_len = 0;

// Labels for discovered dups
static u32 print_dup_labels[PRINT_MAX_DUPS];

// Fresh name counters
static u32 print_fresh_lam = 0;  // lowercase: 1='a', 2='b', ...
static u32 print_fresh_dup = 0;  // uppercase: 27='A', 28='B', ...

fn void print_reset(void) {
  print_lam_count = 0;
  print_dup_count = 0;
  print_dup_queue_len = 0;
  print_dup_seen_len = 0;
  print_fresh_lam = 0;
  print_fresh_dup = 0;
}

// Get or create lowercase name for a LAM/VAR body location
fn u32 print_get_lam_name(u32 loc) {
  for (u32 i = 0; i < print_lam_count; i++) {
    if (print_lam_locs[i] == loc) return print_lam_names[i];
  }
  // Create new name
  u32 name = 1 + print_fresh_lam++;  // 1='a', 2='b', ...
  if (print_lam_count < PRINT_MAX_NAMES) {
    print_lam_locs[print_lam_count] = loc;
    print_lam_names[print_lam_count] = name;
    print_lam_count++;
  }
  return name;
}

// Get or create uppercase name for a DUP/CO0/CO1 location
fn u32 print_get_dup_name(u32 loc) {
  for (u32 i = 0; i < print_dup_count; i++) {
    if (print_dup_locs[i] == loc) return print_dup_names[i];
  }
  // Create new name
  u32 name = 27 + print_fresh_dup++;  // 27='A', 28='B', ...
  if (print_dup_count < PRINT_MAX_NAMES) {
    print_dup_locs[print_dup_count] = loc;
    print_dup_names[print_dup_count] = name;
    print_dup_count++;
  }
  return name;
}

// Check if dup location has been seen
fn int print_dup_is_seen(u32 loc) {
  for (u32 i = 0; i < print_dup_seen_len; i++) {
    if (print_dup_seen[i] == loc) return 1;
  }
  return 0;
}

// Mark dup location as seen and add to queue (with label)
fn void print_discover_dup_with_label(u32 loc, u32 lab) {
  if (print_dup_is_seen(loc)) return;
  if (print_dup_seen_len < PRINT_MAX_DUPS) {
    print_dup_seen[print_dup_seen_len] = loc;
    print_dup_labels[print_dup_seen_len] = lab;
    print_dup_seen_len++;
  }
  if (print_dup_queue_len < PRINT_MAX_DUPS) {
    print_dup_queue[print_dup_queue_len++] = loc;
  }
}

// Get stored label for a dup location
fn u32 print_get_dup_label(u32 loc) {
  for (u32 i = 0; i < print_dup_seen_len; i++) {
    if (print_dup_seen[i] == loc) return print_dup_labels[i];
  }
  return 0;  // default label
}

// Substitution list lookup for book printing (de Bruijn indexed)
// Returns heap location for de Bruijn index `idx`, 0 if not found
fn u32 print_subst_lookup(u32 ls_loc, u32 idx) {
  // Walk list `idx` times to reach the binding
  for (u32 i = 0; i < idx && ls_loc != 0; i++) {
    u64 packed = HEAP[ls_loc];
    ls_loc = (u32)(packed & 0xFFFFFFFF);  // next pointer
  }
  if (ls_loc == 0) return 0;
  return (u32)(HEAP[ls_loc] >> 32);  // value (heap location)
}

// Forward declarations
fn void print_term_go_ex(FILE *f, Term term, u32 ls_loc);
fn void print_ctr_ex(FILE *f, Term t, u32 ls_loc);

fn void print_mat_name(FILE *f, u32 nam) {
  if (nam == NAM_ZER) fputs("0n", f);
  else if (nam == NAM_SUC) fputs("1n+", f);
  else if (nam == NAM_NIL) fputs("[]", f);
  else if (nam == NAM_CON) fputs("<>", f);
  else { fputc('#', f); print_name(f, nam); }
}

// Print substitution list as comma-separated heap location names (de Bruijn order)
fn void print_subst_list(FILE *f, u32 ls_loc) {
  int first = 1;
  while (ls_loc != 0) {
    u64 packed = HEAP[ls_loc];
    u32 heap_loc = (u32)(packed >> 32);        // upper 32 bits: value
    u32 next = (u32)(packed & 0xFFFFFFFF);     // lower 32 bits: next

    if (!first) fputc(',', f);
    first = 0;

    // Print the heap location's name
    u32 name = print_get_lam_name(heap_loc);
    print_name(f, name);

    ls_loc = next;
  }
}

// Prints APP and DRY chains as f(x,y,z)
fn void print_app_ex(FILE *f, Term term, u32 ls_loc) {
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
    print_term_go_ex(f, curr, ls_loc);
    fputc(')', f);
  } else {
    print_term_go_ex(f, curr, ls_loc);
  }
  fputc('(', f);
  for (u32 i = 0; i < len; i++) {
    if (i > 0) {
      fputc(',', f);
    }
    print_term_go_ex(f, spine[len - 1 - i], ls_loc);
  }
  fputc(')', f);
}

fn void print_term_go_ex(FILE *f, Term term, u32 ls_loc) {
  switch (term_tag(term)) {
    case NAM: {
      // Print stuck variable as just the name
      print_name(f, term_ext(term));
      break;
    }
    case DRY: {
      // Print stuck application as f(x,y)
      print_app_ex(f, term, ls_loc);
      break;
    }
    case VAR: {
      u32 loc = term_val(term);
      if (ls_loc != 0) {
        // Book mode: VAL is de Bruijn index, look up in substitution list
        u32 heap_loc = print_subst_lookup(ls_loc, loc);
        if (heap_loc != 0) {
          loc = heap_loc;  // Use substituted heap location for naming
        }
        // If not found, loc remains the de Bruijn index (won't name well, but won't crash)
      }
      // In heap mode or after substitution: loc is heap location
      u32 name = print_get_lam_name(loc);
      print_name(f, name);
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
      u8 side = (term_tag(term) == CO0) ? 0 : 1;

      if (ls_loc != 0) {
        // Book mode: VAL is de Bruijn index, look up in substitution list
        u32 heap_loc = print_subst_lookup(ls_loc, loc);
        if (heap_loc != 0) {
          loc = heap_loc;  // Use substituted heap location
        }
        // If not found, loc remains the de Bruijn index
      }

      // Follow chains (both heap mode and after book substitution)
      Term val = HEAP[loc];
      while (term_sub(val) && (term_tag(term_unmark(val)) == CO0 || term_tag(term_unmark(val)) == CO1)) {
        Term uval = term_unmark(val);
        u8 chain_side = (term_tag(uval) == CO0) ? 0 : 1;
        side ^= chain_side;
        loc = term_val(uval);
        lab = term_ext(uval);
        val = HEAP[loc];
      }
      print_discover_dup_with_label(loc, lab);

      u32 name = print_get_dup_name(loc);
      print_name(f, name);
      if (side == 0) {
        fputs("\xe2\x82\x80", f);  // ₀
      } else {
        fputs("\xe2\x82\x81", f);  // ₁
      }
      break;
    }
    case LAM: {
      u32 loc = term_val(term);
      u32 ext = term_ext(term);
      u32 name;
      if (ext > 0) {
        // Quoted lambda (ext holds the variable name)
        name = ext;
      } else {
        // Normal/book lambda - use location-based naming
        name = print_get_lam_name(loc);
      }
      fputs("λ", f);
      print_name(f, name);
      fputc('.', f);
      print_term_go_ex(f, HEAP[loc], ls_loc);
      break;
    }
    case APP: {
      print_app_ex(f, term, ls_loc);
      break;
    }
    case SUP: {
      u32 loc = term_val(term);
      fputc('&', f);
      print_name(f, term_ext(term));
      fputc('{', f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputc(',', f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc('}', f);
      break;
    }
    case DUP: {
      u32 loc = term_val(term);
      u32 name = print_get_dup_name(loc);
      fputc('!', f);
      print_name(f, name);
      fputc('&', f);
      print_name(f, term_ext(term));
      fputc('=', f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputc(';', f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      break;
    }
    case MAT:
    case SWI: {
      fputs("λ{", f);
      Term cur = term;
      while (term_tag(cur) == MAT || term_tag(cur) == SWI) {
        u32 loc = term_val(cur);
        if (term_tag(cur) == SWI) fprintf(f, "%u", term_ext(cur));
        else print_mat_name(f, term_ext(cur));
        fputc(':', f);
        print_term_go_ex(f, HEAP[loc + 0], ls_loc);
        Term next = HEAP[loc + 1];
        if (term_tag(next) == MAT || term_tag(next) == SWI) fputc(';', f);
        cur = next;
      }
      // Handle tail: NUM(0) = empty, USE = wrapped default, other = default
      if (term_tag(cur) == NUM && term_val(cur) == 0) {
        // empty default - just close
      } else if (term_tag(cur) == USE) {
        fputc(';', f);
        print_term_go_ex(f, HEAP[term_val(cur)], ls_loc);
      } else {
        fputc(';', f);
        print_term_go_ex(f, cur, ls_loc);
      }
      fputc('}', f);
      break;
    }
    case USE: {
      u32 loc = term_val(term);
      fputs("λ{", f);
      print_term_go_ex(f, HEAP[loc], ls_loc);
      fputc('}', f);
      break;
    }
    case C00 ... C16: {
      print_ctr_ex(f, term, ls_loc);
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
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      if (opr < 17) fputs(op_syms[opr], f);
      else fprintf(f, "?%u", opr);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(')', f);
      break;
    }
    case DSU: {
      u32 loc = term_val(term);
      fputs("&(", f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs("){", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(',', f);
      print_term_go_ex(f, HEAP[loc + 2], ls_loc);
      fputc('}', f);
      break;
    }
    case DDU: {
      u32 loc = term_val(term);
      fputs("!(", f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs(")=", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(';', f);
      print_term_go_ex(f, HEAP[loc + 2], ls_loc);
      break;
    }
    case ALO: {
      // Print book term with substitution context: @{a→b;c→d}<term>
      u32 alo_loc = term_val(term);
      u64 pair = HEAP[alo_loc];
      u32 tm_loc = (u32)(pair & 0xFFFFFFFF);
      u32 alo_ls_loc = (u32)(pair >> 32);

      fputs("@{", f);
      print_subst_list(f, alo_ls_loc);
      fputc('}', f);

      // Print the book term with substitution context
      print_term_go_ex(f, HEAP[tm_loc], alo_ls_loc);
      break;
    }
    case RED: {
      u32 loc = term_val(term);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs("~>", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      break;
    }
    case EQL: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs("===", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(')', f);
      break;
    }
    case AND: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs(".&.", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(')', f);
      break;
    }
    case OR: {
      u32 loc = term_val(term);
      fputc('(', f);
      print_term_go_ex(f, HEAP[loc + 0], ls_loc);
      fputs(".|.", f);
      print_term_go_ex(f, HEAP[loc + 1], ls_loc);
      fputc(')', f);
      break;
    }
    case UNS: {
      u32 loc = term_val(term);
      // UNS body is λf.λv.actual_body - extract names from depths
      Term lam_f = HEAP[loc];
      u32 loc_f = term_val(lam_f);
      u32 nam_f = print_get_lam_name(loc_f);
      Term lam_v = HEAP[loc_f];
      u32 loc_v = term_val(lam_v);
      u32 nam_v = print_get_lam_name(loc_v);
      Term body = HEAP[loc_v];
      fputs("! ", f);
      print_name(f, nam_f);
      fputs(" = λ ", f);
      print_name(f, nam_v);
      fputs(" ; ", f);
      print_term_go_ex(f, body, ls_loc);
      break;
    }
    case INC: {
      u32 loc = term_val(term);
      fputs("↑", f);
      print_term_go_ex(f, HEAP[loc], ls_loc);
      break;
    }
  }
}

// Wrapper for heap mode (ls_loc = 0)
fn void print_term_go(FILE *f, Term term) {
  print_term_go_ex(f, term, 0);
}

fn void print_ctr_ex(FILE *f, Term t, u32 ls_loc) {
  u32 nam = term_ext(t), loc = term_val(t), ari = term_tag(t) - C00;
  // Nat: count SUCs, print as Nn or Nn+x
  if (nam == NAM_ZER || nam == NAM_SUC) {
    u32 n = 0;
    while (term_tag(t) == C01 && term_ext(t) == NAM_SUC) { n++; t = HEAP[term_val(t)]; }
    fprintf(f, "%un", n);
    if (!(term_tag(t) == C00 && term_ext(t) == NAM_ZER)) { fputc('+', f); print_term_go_ex(f, t, ls_loc); }
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
      if (!(term_tag(h) == C01 && term_ext(h) == NAM_CHR)) { is_str = 0; break; }
      if (term_tag(HEAP[term_val(h)]) != NUM) { is_str = 0; break; }
      u32 c = term_val(HEAP[term_val(h)]);
      if (c < 32 || c == 127) { is_str = 0; break; }
    }
    Term end = t;
    while (term_tag(end) == C02 && term_ext(end) == NAM_CON)
      end = HEAP[term_val(end)+1];
    if (is_str && term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('"', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1])
        print_utf8(f, term_val(HEAP[term_val(HEAP[term_val(x)])]));
      fputc('"', f);
      return;
    }
    // Proper list: [a,b,c]
    if (term_tag(end) == C00 && term_ext(end) == NAM_NIL) {
      fputc('[', f);
      for (Term x = t; term_tag(x) == C02; x = HEAP[term_val(x)+1]) {
        if (x != t) fputc(',', f);
        print_term_go_ex(f, HEAP[term_val(x)], ls_loc);
      }
      fputc(']', f);
      return;
    }
    // Improper list: h<>t
    if (nam == NAM_CON) {
      print_term_go_ex(f, HEAP[loc], ls_loc); fputs("<>", f); print_term_go_ex(f, HEAP[loc+1], ls_loc);
      return;
    }
  }
  // Default CTR
  fputc('#', f); print_name(f, nam); fputc('{', f);
  for (u32 i = 0; i < ari; i++) { if (i) fputc(',', f); print_term_go_ex(f, HEAP[loc+i], ls_loc); }
  fputc('}', f);
}

fn void print_ctr(FILE *f, Term t) {
  print_ctr_ex(f, t, 0);
}

fn void print_term_to(FILE *f, Term term) {
  print_reset();
  print_term_go(f, term);

  // Print discovered dups (on same line, no spaces)
  // Process queue - may grow as we print more dups
  u32 processed = 0;
  while (processed < print_dup_queue_len) {
    u32 loc = print_dup_queue[processed++];
    u32 name = print_get_dup_name(loc);
    u32 lab = print_get_dup_label(loc);

    fputc('!', f);
    print_name(f, name);
    fputc('&', f);
    print_name(f, lab);
    fputc('=', f);
    print_term_go(f, HEAP[loc]);
    fputc(';', f);
  }
}

fn void print_term(Term term) {
  print_term_to(stdout, term);
}
