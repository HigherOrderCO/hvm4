fn Term parse_term(PState *s, u32 depth);
fn Term parse_term_lam_go(PState *s, u32 depth);
fn Term parse_term_lam_simple(Term f, PState *s, u32 depth, int min_prec);
fn Term parse_term_lam_dupped(Term f, PState *s, u32 depth, int min_prec);

fn Term parse_term_lam(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  // λ[&]x.f
  // λ[&]x&L.f
  // λ[&]x&(L).f
  if (!parse_match(s, "λ")) return 0; //
  return parse_term_lam_go(s, depth);
}

fn Term parse_term_lam_go(PState *s, u32 depth) {
  Parser atoms[] = {
    parse_term_lam_dupped, // λ[&]x&[L|(L)].f
    parse_term_lam_simple, // λ[&]x.f
    NULL
  };
  return parse_choice(NONE, s, depth, 0, atoms);
}

fn Term parse_term_lam_simple(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  parse_skip(s);
  // Parse argument: [&]name[&[label|(label)]]
  u32 cloned = parse_match(s, "&");
  u32 nam    = parse_name(s);
  parse_skip(s);
  // Simple single arg (with comma recursion for cloned/complex args)
  parse_bind_push(nam, depth, 0, cloned);
  Term body;
  if (parse_match(s, ",")) {
    body = parse_term_lam_go(s, depth + 1);
  } else {
    parse_consume(s, ".");
    body = parse_term(s, depth + 1);
  }
  u32 uses = parse_bind_get_uses();
  if (!cloned && uses > 1) {
    parse_error(s, PERR_AFFINE(nam, uses, "λ&"));
  }
  if (cloned && uses > 1) {
    body = parse_auto_dup(body, 0, uses, VAR, 0);
  }
  parse_bind_pop();
  u64 loc = heap_alloc(1);
  HEAP[loc] = body;
  return term_new(0, LAM, depth, loc);
}

fn Term parse_term_lam_dupped(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  // Inline dup: λx&L or λx&(L) or λx&
  parse_skip(s);
  // Parse argument: [&]name[&[label|(label)]]
  u32 cloned = parse_match(s, "&");
  u32 nam    = parse_name(s);
  parse_skip(s);
  if (!parse_match(s, "&")) return 0;
  parse_skip(s);
  int  dyn      = parse_peek(s) == '(';
  Term lab_term = 0;
  u32  lab      = 0;
  if (dyn) {
    parse_consume(s, "(");
    lab_term = parse_term(s, depth + 1);  // +1 because we're inside the outer lambda
    parse_consume(s, ")");
  } else {
    char c = parse_peek(s);
    if (c == ',' || c == '.') {
      lab = PARSE_FRESH_LAB++;
    } else {
      lab = parse_name(s);
    }
  }
  parse_skip(s);
  u32 d = dyn ? 3 : 2;
  parse_bind_push(nam, depth + 1, dyn ? 0xFFFFFF : lab, cloned);
  Term body;
  if (parse_match(s, ",")) {
    body = parse_term_lam_go(s, depth + d);
  } else {
    parse_consume(s, ".");
    body = parse_term(s, depth + d);
  }
  u32 uses  = parse_bind_get_uses();
  u32 uses0 = parse_bind_get_uses0();
  u32 uses1 = parse_bind_get_uses1();
  parse_bind_pop();
  if (dyn) {
    if (cloned && uses0 > 1) {
      body = parse_auto_dup(body, 1, uses0, VAR, 0);
    }
    if (cloned && uses1 > 1) {
      body = parse_auto_dup(body, 0, uses1, VAR, 0);
    }
    u64 loc1 = heap_alloc(1);
    HEAP[loc1] = body;
    u64 loc0 = heap_alloc(1);
    HEAP[loc0] = term_new(0, LAM, depth + 2, loc1);
    Term ddu = term_new_ddu(lab_term, term_new(0, VAR, 0, 0), term_new(0, LAM, depth + 1, loc0));
    u64 lam_loc = heap_alloc(1);
    HEAP[lam_loc] = ddu;
    return term_new(0, LAM, depth, lam_loc);
  } else {
    if (!cloned && uses > 2) {
      parse_error(s, PERR_AFFINE_DUP(nam, uses));
    }
    if (cloned && uses1 > 1) {
      body = parse_auto_dup(body, 0, uses1, CO1, lab);
    }
    if (cloned && uses0 > 1) {
      body = parse_auto_dup(body, 0, uses0, CO0, lab);
    }
    u64 dup_loc = heap_alloc(2);
    HEAP[dup_loc + 0] = term_new(0, VAR, 0, 0);
    HEAP[dup_loc + 1] = body;
    u64 lam_loc = heap_alloc(1);
    HEAP[lam_loc] = term_new(0, DUP, lab, dup_loc);
    return term_new(0, LAM, depth, lam_loc);
  }
}
