fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_let(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "!")) return 0;
  parse_skip(s);
  // Check for !!x = val or !!&x = val (strict let, optionally cloned)
  int strict = parse_match(s, "!");
  parse_skip(s);
  // Check for cloned: & comes BEFORE name
  // Cloned let: ! &x = val
  u32 cloned = 0;
  if (parse_peek(s) == '&') {
    parse_advance(s);  // consume &
    parse_skip(s);
    cloned = 1;
  }
  u32 nam = parse_name(s);
  parse_skip(s);
  if (!parse_match(s, "=")) return 0;

  Term val = parse_term(s, depth);
  parse_skip(s);
  parse_match(s, ";");
  parse_bind_push(nam, depth, 0, cloned);
  u64  loc  = heap_alloc(1);
  Term body = parse_term(s, depth + 1);
  u32  uses = parse_bind_get_uses();
  // Check for affinity violation on non-cloned variables
  if (!cloned && uses > 1) {
    parse_error(s, PERR_AFFINE(nam, uses, "! &"));
  }
  // Apply auto-dup transformation for cloned variables with multiple uses
  if (cloned && uses > 1) {
    body = parse_auto_dup(body, 0, uses, VAR, 0);
  }
  HEAP[loc] = body;
  parse_bind_pop();
  Term lam = term_new(0, LAM, depth, loc);
  if (strict) {
    // !!x = val; body  →  (λ{λx.body(x)})(val)
    lam = term_new_use(lam);
  }
  return term_new_app(lam, val);
}

