fn Term parse_term(PState *s, u32 depth);
fn u32  parse_char_lit(PState *s);

fn Term parse_term_lam(PState *s, u32 depth) {
  parse_skip(s);
  // Era λ{}, Use λ{f} or Lambda-match λ{A:f; B:g; ...; i}
  if (parse_peek(s) == '{') {
    parse_consume(s, "{");
    parse_skip(s);
    if (parse_peek(s) == '}') {
      parse_consume(s, "}");
      return term_new_era();
    }
    Term  term = term_new_num(0);
    Term *tip  = &term;
    while (1) {
      parse_skip(s);
      u8  tag = 0;
      u32 ext = 0;
      if (parse_peek(s) == '\'') {
        u32 sav = s->pos;
        u32 code = parse_char_lit(s);
        parse_skip(s);
        if (parse_peek(s) == ':') {
          tag = SWI;
          ext = code;
        } else {
          s->pos = sav;
        }
      }
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
          } else if (ext == 1 && parse_peek_at(s, 1) == '+') {
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

  // Parse argument: [&]name[&[label|(label)]]
  u32 cloned = parse_match(s, "&");
  u32 nam    = parse_name(s);
  parse_skip(s);

  // Inline dup: λx&L or λx&(L) or λx&
  if (parse_peek(s) == '&') {
    parse_advance(s);
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
    PBind* bind = parse_bind_push(nam, depth + 1, dyn ? 0xFFFFFF : lab, 0, cloned);
    Term body;
    if (parse_match(s, ",")) {
      body = parse_term_lam(s, depth + d);
    } else {
      parse_consume(s, ".");
      body = parse_term(s, depth + d);
    }
    u32 uses = bind->uses;
    parse_bind_pop();
    if (dyn) {
      if (cloned) {
        body = parse_auto_dup(body, depth + 2, depth + 3, BJV, 0);
        body = parse_auto_dup(body, depth + 3, depth + 3, BJV, 0);
      }
      u64 loc1 = heap_alloc(1);
      HEAP[loc1] = body;
      u64 loc0 = heap_alloc(1);
      HEAP[loc0] = term_new(0, LAM, depth + 3, loc1);
      Term ddu = term_new_ddu(lab_term, term_new(0, BJV, 0, depth + 1), term_new(0, LAM, depth + 2, loc0));
      u64 lam_loc = heap_alloc(1);
      HEAP[lam_loc] = ddu;
      u32 lam_ext = depth + 1;
      if (uses == 0) {
        lam_ext |= LAM_ERA_MASK;
      }
      return term_new(0, LAM, lam_ext, lam_loc);
    } else {
      if (cloned) {
        body = parse_auto_dup(body, depth + 2, depth + 2, BJ1, lab);
        body = parse_auto_dup(body, depth + 2, depth + 2, BJ0, lab);
      }
      u64 dup_term_loc = heap_alloc(2);
      HEAP[dup_term_loc + 0] = term_new(0, BJV, 0, depth + 1);
      HEAP[dup_term_loc + 1] = body;
      u64 lam_loc = heap_alloc(1);
      HEAP[lam_loc] = term_new(0, DUP, lab, dup_term_loc);
      u32 lam_ext = depth + 1;
      if (uses == 0) {
        lam_ext |= LAM_ERA_MASK;
      }
      return term_new(0, LAM, lam_ext, lam_loc);
    }
  }

  // Simple single arg (with comma recursion for cloned/complex args)
  PBind* bind = parse_bind_push(nam, depth, 0, 0, cloned);
  Term body;
  if (parse_match(s, ",")) {
    body = parse_term_lam(s, depth + 1);
  } else {
    parse_consume(s, ".");
    body = parse_term(s, depth + 1);
  }
  if (cloned) {
    body = parse_auto_dup(body, depth + 1, depth + 1, BJV, 0);
  }
  u32 uses = bind->uses;
  parse_bind_pop();
  u32 lam_ext = depth + 1;
  if (uses == 0) {
    lam_ext |= LAM_ERA_MASK;
  }
  u64 loc = heap_alloc(1);
  HEAP[loc] = body;
  return term_new(0, LAM, lam_ext, loc);
}
