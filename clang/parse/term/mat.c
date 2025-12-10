fn Term parse_term(PState *s, u32 depth);
fn void parse_mat_tag_num(PState *s, u8 *tag, u32 *ext);
fn void parse_mat_tag_ctr(PState *s, u8 *tag, u32 *ext);
fn void parse_mat_tag_nil(PState *s, u8 *tag, u32 *ext);
fn void parse_mat_tag_con(PState *s, u8 *tag, u32 *ext);

fn Term parse_term_mat(Term f, PState *s, u32 depth, int min_prec) {
  (void)f; (void)min_prec;
  if (!parse_match(s, "λ")) return 0;
  parse_skip(s);
  if (!parse_match(s, "{")) return 0;

  Term  term = term_new_num(0);
  Term *tip  = &term;

  while (1) {
    // try to add clause (tag,ext)
    parse_skip(s);
    u8  tag = 0;
    u32 ext = 0;
    if (!tag) { parse_mat_tag_num(s, &tag, &ext); }; // pattern assumes clauses can't have APP (i.e. 0) as tag
    if (!tag) { parse_mat_tag_ctr(s, &tag, &ext); };
    if (!tag) { parse_mat_tag_nil(s, &tag, &ext); };
    if (!tag) { parse_mat_tag_con(s, &tag, &ext); };
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
      // if added clause, seek for the next one
      continue;
    }
    // fail if no clauses added
    if (term == term_new_num(0)) return 0;
    // close mat, no default
    if (parse_peek(s) == '}') {
      parse_consume(s, "}");
      return term;
    }
    // default clause
    if (parse_peek(s) == '_') {
      parse_advance(s);
      parse_skip(s);
      parse_consume(s, ":");
    }
    *tip = parse_term(s, depth);
    // close mat
    parse_skip(s);
    parse_consume(s, "}");
    return term;
  }
}

// Try to parse a numeric matcher: <num>: (SWI) or <num>n / <num>n+ (MAT ZER/SUC)
// Returns if matched and sets tag/ext; otherwise, restores state and returns.
fn void parse_mat_tag_num(PState *s, u8 *tag, u32 *ext) {
  if (!isdigit(parse_peek(s))) return;
  PState st = *s;
  u32 num = 0;
  while (isdigit(parse_peek(s))) {
    num = num * 10 + (parse_peek(s) - '0');
    parse_advance(s);
  }
  parse_skip(s);
  if (parse_peek(s) == ':') {
    *tag = SWI;
    *ext = num;
    return;
  }
  if (parse_peek(s) == 'n') {
    if (num == 0 && parse_peek_at(s, 1) != '+') {
      parse_advance(s);
      *tag = MAT;
      *ext = NAM_ZER;
      return;
    } else if (parse_peek_at(s, 1) == '+') {
      parse_advance(s);
      parse_advance(s);
      *tag = MAT;
      *ext = NAM_SUC;
      return;
    }
  }
  *s = st;
  return;
}

// Try to parse #name matcher
fn void parse_mat_tag_ctr(PState *s, u8 *tag, u32 *ext) {
  if (parse_peek(s) != '#') return;
  parse_advance(s);
  *tag = MAT;
  *ext = parse_name(s);
  return;
}

// Try to parse [] matcher
fn void parse_mat_tag_nil(PState *s, u8 *tag, u32 *ext) {
  if (parse_peek(s) != '[' || parse_peek_at(s, 1) != ']') return;
  parse_advance(s);
  parse_advance(s);
  *tag = MAT;
  *ext = NAM_NIL;
  return;
}

// Try to parse <> matcher
fn void parse_mat_tag_con(PState *s, u8 *tag, u32 *ext) {
  if (parse_peek(s) != '<' || parse_peek_at(s, 1) != '>') return;
  parse_advance(s);
  parse_advance(s);
  *tag = MAT;
  *ext = NAM_CON;
  return;
}
