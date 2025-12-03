fn Term parse_term(PState *s, u32 depth);

// Parse unscoped binding: ! ${f, v}; body
// Creates an UNS term containing λf. λv. body
fn Term parse_term_uns(PState *s, u32 depth) {
  parse_skip(s);
  parse_consume(s, "{");
  parse_skip(s);
  u32 nam_f = parse_name(s);
  parse_skip(s);
  parse_consume(s, ",");
  parse_skip(s);
  u32 nam_v = parse_name(s);
  parse_skip(s);
  parse_consume(s, "}");
  parse_skip(s);
  parse_match(s, ";");
  parse_skip(s);

  parse_bind_push(nam_f, depth, 0, 0);
  parse_bind_push(nam_v, depth + 1, 0, 0);
  u64 loc_f = heap_alloc(1);
  u64 loc_v = heap_alloc(1);
  Term body = parse_term(s, depth + 2);
  parse_bind_pop();
  parse_bind_pop();

  HEAP[loc_v] = body;
  Term lam_v = term_new(0, LAM, depth + 1, loc_v);
  HEAP[loc_f] = lam_v;
  Term lam_f = term_new(0, LAM, depth, loc_f);
  return term_new_uns(lam_f);
}

