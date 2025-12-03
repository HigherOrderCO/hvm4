fn Term parse_term(PState *s, u32 depth);

fn Term parse_term_lam(PState *s, u32 depth) {
  parse_skip(s);
  if (parse_peek(s) == '{') {
    parse_consume(s, "{");
    parse_skip(s);
    if (parse_peek(s) == '}') {
      parse_consume(s, "}");
      return term_new_era();
    }
    // Parse SWI/MAT/USE with chaining
    Term term = term_new_era();
    Term *tip = &term;
    while (1) {
      parse_skip(s);
      u8  tag = 0;
      u32 ext = 0;
      // SWI case: 123:
      if (isdigit(parse_peek(s))) {
        u32 sav = s->pos;
        while (isdigit(parse_peek(s))) {
          ext = ext * 10 + (parse_peek(s) - '0');
          parse_advance(s);
        }
        parse_skip(s);
        if (parse_peek(s) == ':') {
          tag = SWI;
        } else if (parse_peek(s) == 'n') {
          // Nat sugar: 0n or Nn+
          if (ext == 0 && parse_peek_at(s, 1) != '+') {
            parse_advance(s);
            tag = MAT; ext = NAM_ZER;
          } else if (parse_peek_at(s, 1) == '+') {
            parse_advance(s); parse_advance(s);
            tag = MAT; ext = NAM_SUC;
          } else {
            s->pos = sav;
          }
        } else {
          s->pos = sav;
        }
      }
      // MAT cases: #Name, [], <>
      if (!tag && parse_peek(s) == '#') {
        parse_advance(s);
        tag = MAT; ext = parse_name(s);
      }
      if (!tag && parse_peek(s) == '[' && parse_peek_at(s, 1) == ']') {
        parse_advance(s); parse_advance(s);
        tag = MAT; ext = NAM_NIL;
      }
      if (!tag && parse_peek(s) == '<' && parse_peek_at(s, 1) == '>') {
        parse_advance(s); parse_advance(s);
        tag = MAT; ext = NAM_CON;
      }
      // Found a case - parse body and chain
      if (tag) {
        parse_skip(s);
        parse_consume(s, ":");
        Term val = parse_term(s, depth);
        parse_skip(s);
        parse_match(s, ";");
        u64 loc = heap_alloc(2);
        HEAP[loc + 0] = val;
        HEAP[loc + 1] = term_new_era();
        *tip = term_new(0, tag, ext, loc);
        tip  = &HEAP[loc + 1];
        continue;
      }
      // No case found - either }, USE, or default
      if (parse_peek(s) == '}') {
        parse_consume(s, "}");
        return term;
      }
      // Allow _: prefix for default case
      if (parse_peek(s) == '_') {
        parse_advance(s);
        parse_skip(s);
        parse_consume(s, ":");
      }
      if (term == term_new_era()) {
        Term f = parse_term(s, depth);
        parse_skip(s);
        parse_consume(s, "}");
        return term_new_use(f);
      }
      *tip = parse_term(s, depth);
      parse_skip(s);
      parse_consume(s, "}");
      return term;
    }
  }
  // Check for cloned variable: λ&x.body
  u32 cloned = parse_match(s, "&");
  u32 nam = parse_name(s);
  parse_consume(s, ".");
  parse_bind_push(nam, depth, 0, cloned);
  u64  loc  = heap_alloc(1);
  Term body = parse_term(s, depth + 1);
  u32  uses = parse_bind_get_uses();
  // Check for affinity violation on non-cloned variables
  if (!cloned && uses > 1) {
    fprintf(stderr, "\033[1;31mPARSE_ERROR\033[0m\n");
    fprintf(stderr, "- variable '"); print_name(stderr, nam);
    fprintf(stderr, "' used %d times (not cloned)\n", uses);
    fprintf(stderr, "- hint: use λ& to allow multiple uses\n");
    exit(1);
  }
  // Apply auto-dup transformation for cloned variables with multiple uses
  if (cloned && uses > 1) {
    body = parse_auto_dup(body, 0, uses);
  }
  HEAP[loc] = body;
  parse_bind_pop();
  return term_new(0, LAM, depth, loc);
}
