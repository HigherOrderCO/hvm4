fn Term parse_term(PState *s, u32 depth);
fn Term parse_term_uns(PState *s, u32 depth);

fn Term parse_term_dup(PState *s, u32 depth) {
  parse_skip(s);
  // Check for unscoped binding: ! ${f, v}; body
  if (parse_match(s, "$")) {
    return parse_term_uns(s, depth);
  }
  // Check for !!x = val or !!&x = val (strict let, optionally cloned)
  int strict = parse_match(s, "!");
  parse_skip(s);
  // Check for cloned: & comes BEFORE name
  // Cloned let: ! &x = val
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
  // Check for let sugar: ! x = val; body  →  (λx.body)(val)
  // Or cloned let: ! &x = val; body
  if (parse_peek(s) == '=') {
    parse_advance(s);
    Term val = parse_term(s, depth);
    parse_skip(s);
    parse_match(s, ";");
    parse_bind_push(nam, depth, 0, cloned);
    u64  loc  = heap_alloc(1);
    Term body = parse_term(s, depth + 1);
    u32  uses = parse_bind_get_uses();
    // Check for affinity violation on non-cloned variables
    if (!cloned && uses > 1) {
      fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
      fprintf(stderr, "- variable '"); print_name(stderr, nam);
      fprintf(stderr, "' used %d times (not cloned)\n", uses);
      fprintf(stderr, "- hint: use ! & to allow multiple uses\n");
      exit(1);
    }
    // Apply auto-dup transformation for cloned variables with multiple uses
    if (cloned && uses > 1) {
      body = parse_auto_dup(body, 0, uses);
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
  // Regular DUP: !x&label = val; body  or  !x& = val; body (auto-label)
  // Cloned DUP: !&X &label = val; body  or  !&X & = val; body (auto-label)
  // Dynamic DUP: !x&(lab) = val; body  (lab is an expression)
  // Cloned Dynamic DUP: !&X &(lab) = val; body
  parse_consume(s, "&");
  parse_skip(s);
  // Check for dynamic label: &(expr)
  // Syntax: ! X &(lab) = val; ... X₀ ... X₁ ...
  // Desugars to: @dup(lab, val, λx0.λx1. body[X₀→x0, X₁→x1])
  if (parse_peek(s) == '(') {
    parse_consume(s, "(");
    Term lab_term = parse_term(s, depth);
    parse_consume(s, ")");
    parse_consume(s, "=");
    Term val = parse_term(s, depth);
    parse_skip(s);
    parse_match(s, ";");
    parse_skip(s);
    // Use special marker lab=0xFFFFFF to indicate dynamic dup binding
    // The var parser will emit VAR instead of CO0/CO1 for this binding
    // X₀ will have index = depth+2 - 1 - depth = 1 (outer lambda)
    // X₁ will have index = depth+2 - 1 - (depth+1) = 0 (inner lambda)
    // We push binding at 'depth' but body is parsed at depth+2
    parse_bind_push(nam, depth, 0xFFFFFF, cloned);  // dynamic dup marker
    Term body = parse_term(s, depth + 2);
    u32 uses0 = parse_bind_get_uses0();
    u32 uses1 = parse_bind_get_uses1();
    parse_bind_pop();
    // Apply auto-dup for cloned dynamic dup
    // X₀ → VAR(1), X₁ → VAR(0). After first auto-dup wraps in DUPs,
    // the second auto-dup traverses those DUPs (incrementing idx) to find X₁.
    if (cloned && uses0 > 1) {
      body = parse_auto_dup(body, 1, uses0);
    }
    if (cloned && uses1 > 1) {
      body = parse_auto_dup(body, 0, uses1);
    }
    // Generate: DynDup(lab, val, λ_.λ_.body)
    u64 loc0     = heap_alloc(1);
    u64 loc1     = heap_alloc(1);
    HEAP[loc1]   = body;
    Term lam1    = term_new(0, LAM, depth + 1, loc1);
    HEAP[loc0]   = lam1;
    Term lam0    = term_new(0, LAM, depth, loc0);
    return term_new_ddu(lab_term, val, lam0);
  }
  // Static label
  u32 lab;
  if (parse_peek(s) == '=') {
    lab = PARSE_FRESH_LAB++;
  } else {
    lab = parse_name(s);
  }
  parse_consume(s, "=");
  Term val = parse_term(s, depth);
  parse_skip(s);
  parse_match(s, ";");
  parse_skip(s);
  parse_bind_push(nam, depth, lab, cloned);  // Pass cloned flag
  u64 loc       = heap_alloc(2);
  HEAP[loc + 0] = val;
  Term body     = parse_term(s, depth + 1);
  u32 uses  = parse_bind_get_uses();
  u32 uses0 = parse_bind_get_uses0();
  u32 uses1 = parse_bind_get_uses1();
  // Check for affinity violation on non-cloned dup bindings
  if (!cloned && uses > 2) {
    fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
    fprintf(stderr, "- dup variable '"); print_name(stderr, nam);
    fprintf(stderr, "' used %d times (max 2 with ₀ and ₁)\n", uses);
    exit(1);
  }
  if (cloned && (uses0 < 1 || uses1 < 1)) {
    // For cloned dup, both sides must be used at least once
    // (otherwise it's not really a dup, just use a let)
    // Actually, let's be lenient and allow unused sides
  }
  // Apply auto-dup for cloned dup bindings
  // The DUP traversal in parse_auto_dup_co naturally handles depth, so both
  // transformations pass idx=0. The first transformation wraps in DUP nodes,
  // and the second transformation traverses through those DUPs to find the
  // remaining CO references at the correct depth.
  if (cloned && uses1 > 1) {
    body = parse_auto_dup_co(body, 0, uses1, lab, CO1);
  }
  if (cloned && uses0 > 1) {
    body = parse_auto_dup_co(body, 0, uses0, lab, CO0);
  }
  HEAP[loc + 1] = body;
  parse_bind_pop();
  return term_new(0, DUP, lab, loc);
}
