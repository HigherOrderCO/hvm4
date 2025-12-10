fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_dup(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "!")) return 0;
  parse_skip(s);
  // Check for cloned: & comes BEFORE name
  // Cloned dup: ! &X &L = val  or  ! &X &(L) = val
  // Regular dup: !x& = val
  u32 cloned = 0;
  if (parse_peek(s) == '&') {
    parse_advance(s);  // consume &
    parse_skip(s);
    cloned = 1;
  }
  u32 nam = parse_name(s);
  parse_skip(s);
  if (!parse_match(s, "&")) return 0;

  // Helper: parse dup after & is consumed. Expects: [(label)] [=val;] body
  // If val is provided (non-zero loc), uses it; otherwise parses "= val;" from input.
  // For λx&L.F sugar, val_loc points to where VAR(0) should go.
  u64 val_loc = 0;

  parse_skip(s);
  // Dynamic label: (expr)
  if (parse_peek(s) == '(') {
    parse_consume(s, "(");
    Term lab_term = parse_term(s, depth);
    parse_consume(s, ")");
    Term val;
    if (val_loc) {
      val = HEAP[val_loc];
      parse_consume(s, ".");
    } else {
      parse_consume(s, "=");
      val = parse_term(s, depth);
      parse_skip(s);
      parse_match(s, ";");
    }
    parse_skip(s);
    parse_bind_push(nam, depth, 0xFFFFFF, cloned);
    Term body = parse_term(s, depth + 2);
    u32 uses0 = parse_bind_get_uses0();
    u32 uses1 = parse_bind_get_uses1();
    parse_bind_pop();
    if (cloned && uses0 > 1) {
      body = parse_auto_dup(body, 1, uses0, VAR, 0);
    }
    if (cloned && uses1 > 1) {
      body = parse_auto_dup(body, 0, uses1, VAR, 0);
    }
    u64 loc0   = heap_alloc(1);
    u64 loc1   = heap_alloc(1);
    HEAP[loc1] = body;
    Term lam1  = term_new(0, LAM, depth + 1, loc1);
    HEAP[loc0] = lam1;
    Term lam0  = term_new(0, LAM, depth, loc0);
    return term_new_ddu(lab_term, val, lam0);
  }
  // Static label (or auto if next is = or .)
  u32 lab;
  char c = parse_peek(s);
  if (c == '=' || c == '.') {
    lab = PARSE_FRESH_LAB++;
  } else {
    lab = parse_name(s);
  }
  Term val;
  u64 loc = heap_alloc(2);
  if (val_loc) {
    HEAP[loc] = HEAP[val_loc];
    parse_consume(s, ".");
  } else {
    parse_consume(s, "=");
    HEAP[loc] = parse_term(s, depth);
    parse_skip(s);
    parse_match(s, ";");
  }
  parse_skip(s);
  parse_bind_push(nam, depth, lab, cloned);
  Term body     = parse_term(s, depth + 1);
  u32 uses      = parse_bind_get_uses();
  u32 uses0     = parse_bind_get_uses0();
  u32 uses1     = parse_bind_get_uses1();
  if (!cloned && uses > 2) {
    parse_error(s, PERR_AFFINE_DUP(nam, uses));
  }
  if (cloned && uses1 > 1) {
    body = parse_auto_dup(body, 0, uses1, CO1, lab);
  }
  if (cloned && uses0 > 1) {
    body = parse_auto_dup(body, 0, uses0, CO0, lab);
  }
  HEAP[loc + 1] = body;
  parse_bind_pop();
  return term_new(0, DUP, lab, loc);
}

