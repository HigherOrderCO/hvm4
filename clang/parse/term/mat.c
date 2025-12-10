fn Term parse_term(PState *s, u32 depth);

// Mat body: assumes λ already consumed
// Parses: {#K: ...; ...} or {0: ...; ...}
fn Term parse_term_mat_body(PState *s, u32 depth) {
  parse_skip(s);
  if (!parse_match(s, "{")) return 0;

  Term  term = term_new_num(0);
  Term *tip  = &term;
  while (1) {
    parse_skip(s);
    u8  tag = 0;
    u32 ext = 0;
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
        if (ext == 0 && parse_peek_at(s, 1) != '+') {
          parse_advance(s);
          tag = MAT;
          ext = NAM_ZER;
        } else if (parse_peek_at(s, 1) == '+') {
          parse_advance(s);
          parse_advance(s);
          tag = MAT;
          ext = NAM_SUC;
        } else {
          s->pos = sav;
        }
      } else {
        s->pos = sav;
      }
    }
    if (!tag && parse_peek(s) == '#') {
      parse_advance(s);
      tag = MAT;
      ext = parse_name(s);
    }
    if (!tag && parse_peek(s) == '[' && parse_peek_at(s, 1) == ']') {
      parse_advance(s);
      parse_advance(s);
      tag = MAT;
      ext = NAM_NIL;
    }
    if (!tag && parse_peek(s) == '<' && parse_peek_at(s, 1) == '>') {
      parse_advance(s);
      parse_advance(s);
      tag = MAT;
      ext = NAM_CON;
    }
    if (tag) {
      parse_skip(s);
      parse_consume(s, ":");
      Term val = parse_term(s, depth);
      parse_skip(s);
      parse_match(s, ";");
      u64 loc = heap_alloc(2);
      HEAP[loc + 0] = val;
      HEAP[loc + 1] = term_new_num(0);
      *tip = term_new(0, tag, ext, loc);
      tip  = &HEAP[loc + 1];
      continue;
    }
    if (parse_peek(s) == '}') {
      parse_consume(s, "}");
      return term;
    }
    if (parse_peek(s) == '_') {
      parse_advance(s);
      parse_skip(s);
      parse_consume(s, ":");
    }
    if (term == term_new_num(0)) {
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
