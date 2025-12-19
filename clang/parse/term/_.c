// Parse a single atom (no trailing operators or function calls)
fn Term parse_term_atom(PState *s, u32 depth) {
  parse_skip(s);
  if (parse_match(s, "λ")) {
    return parse_term_lam(s, depth);
  } else if (parse_match(s, "!")) {
    return parse_term_dup(s, depth);
  } else if (parse_match(s, "&")) {
    return parse_term_sup(s, depth);
  } else if (parse_match(s, "#")) {
    return parse_term_ctr(s, depth);
  } else if (parse_match(s, "@")) {
    return parse_term_ref(s);
  } else if (parse_match(s, "^")) {
    return parse_term_nam(s, depth);
  } else if (parse_match(s, "↑")) {
    return parse_term_inc(s, depth);
  } else if (parse_match(s, "*")) {
    return parse_term_any();
  } else if (parse_match(s, "(")) {
    return parse_term_par(s, depth);
  } else if (parse_peek(s) == '[') {
    return parse_term_lst(s, depth);
  } else if (parse_peek(s) == '\'') {
    return parse_term_chr(s);
  } else if (parse_peek(s) == '"') {
    return parse_term_str(s, depth);
  } else if (isdigit(parse_peek(s))) {
    Term t = parse_term_nat(s, depth);
    if (!t) t = parse_term_num(s);
    return t;
  } else {
    return parse_term_var(s, depth);
  }
}

fn Term parse_term(PState *s, u32 depth) {
  return parse_term_app(parse_term_atom(s, depth), s, depth);
}
