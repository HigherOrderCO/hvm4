fn Term parse_term(PState *s, u32 depth);

// Fork: &Lλx,y,z{A;B} or &(L)λx,y,z{A;B}
// Desugars to: λx&L.λy&L.λz&L.&L{A';B'}
// where A' uses x₀,y₀,z₀ and B' uses x₁,y₁,z₁
fn Term parse_term_frk(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "&")) return 0;
  int  dyn      = parse_peek(s) == '(';
  Term lab_term = 0;
  u32  lab      = 0;
  if (dyn) {
    parse_consume(s, "(");
    lab_term = parse_term(s, depth);
    parse_consume(s, ")");
  } else {
    lab = parse_name(s);
  }
  parse_skip(s);
  if (!parse_match(s, "λ")) return 0;

  u32 names[16];
  u32 n = 0;
  names[n++] = parse_name(s);
  parse_skip(s);
  while (parse_peek(s) != '{') {
    parse_match(s, ",");  // optional comma between names
    parse_skip(s);
    if (parse_peek(s) == '{') break;
    names[n++] = parse_name(s);
    parse_skip(s);
  }
  parse_consume(s, "{");
  u32 d = dyn ? 3 : 2;
  for (u32 i = 0; i < n; i++) {
    parse_bind_push(names[i], depth + i * d + 1, dyn ? 0xFFFFFF : lab, 0);
  }
  u32 body_depth = depth + n * d;
  // Optional &₀: before left branch
  parse_match(s, "&₀:");
  PARSE_FORK_SIDE = 0;
  Term left = parse_term(s, body_depth);
  parse_skip(s);
  parse_match(s, ";");  // optional semicolon between branches
  parse_skip(s);
  // Optional &₁: before right branch
  parse_match(s, "&₁:");
  PARSE_FORK_SIDE = 1;
  Term right = parse_term(s, body_depth);
  PARSE_FORK_SIDE = -1;
  parse_skip(s);
  parse_match(s, ";");  // optional trailing semicolon
  parse_consume(s, "}");
  for (u32 i = 0; i < n; i++) {
    parse_bind_pop();
  }
  // Build body: DSU or SUP
  Term body;
  if (dyn) {
    Term dsu_lab = (term_tag(lab_term) == VAR)
      ? term_new(0, VAR, 0, term_val(lab_term) + n * d)
      : lab_term;
    body = term_new_dsu(dsu_lab, left, right);
  } else {
    body = term_new_sup(lab, left, right);
  }
  // Wrap with λ&L or λ&(L) for each arg (reverse order)
  for (int i = n - 1; i >= 0; i--) {
    u32 dd = depth + i * d;
    if (dyn) {
      Term adj_lab = (term_tag(lab_term) == VAR)
        ? term_new(0, VAR, 0, term_val(lab_term) + i * d + 1)
        : lab_term;
      u64 loc1 = heap_alloc(1);
      HEAP[loc1] = body;
      u64 loc0 = heap_alloc(1);
      HEAP[loc0] = term_new(0, LAM, dd + 2, loc1);
      Term ddu = term_new_ddu(adj_lab, term_new(0, VAR, 0, 0), term_new(0, LAM, dd + 1, loc0));
      u64 lam_loc = heap_alloc(1);
      HEAP[lam_loc] = ddu;
      body = term_new(0, LAM, dd, lam_loc);
    } else {
      u64 dup_loc = heap_alloc(2);
      HEAP[dup_loc + 0] = term_new(0, VAR, 0, 0);
      HEAP[dup_loc + 1] = body;
      u64 lam_loc = heap_alloc(1);
      HEAP[lam_loc] = term_new(0, DUP, lab, dup_loc);
      body = term_new(0, LAM, dd, lam_loc);
    }
  }
  return body;
}
