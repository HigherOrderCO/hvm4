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
    Term mat = term_new_era();
    Term *tip = &mat;
    while (1) {
      parse_skip(s);
      if (parse_peek(s) == '#') {
        parse_consume(s, "#");
        u32  nam = parse_name(s);
        parse_consume(s, ":");
        Term val = parse_term(s, depth);
        parse_skip(s);
        parse_match(s, ";");
        u64 loc = heap_alloc(2);
        HEAP[loc + 0] = val;
        HEAP[loc + 1] = term_new_era();
        *tip = term_new(0, MAT, nam, loc);
        tip = &HEAP[loc + 1];
      } else if (parse_peek(s) == '}') {
        parse_consume(s, "}");
        return mat;
      } else {
        *tip = parse_term(s, depth);
        parse_consume(s, "}");
        return mat;
      }
    }
  }
  u32 nam = parse_name(s);
  parse_consume(s, ".");
  parse_bind_push(nam, depth, 0);
  u64  loc  = heap_alloc(1);
  Term body = parse_term(s, depth + 1);
  HEAP[loc] = body;
  parse_bind_pop();
  return term_new(0, LAM, depth, loc);
}
