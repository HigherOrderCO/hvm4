// Parse a single atom (no trailing operators or function calls)
fn Term parse_term_atom(PState *s, u32 depth) {
  parse_skip(s);

  TermParser atoms[] = { 
    parse_term_any,
    parse_term_era,
    parse_term_mat,
    parse_term_lam,
    parse_term_dup,
    parse_term_fork,
    parse_term_sup,
    parse_term_ctr,
    parse_term_ref,
    parse_term_nam,
    parse_term_par,
    parse_term_lst,
    parse_term_chr,
    parse_term_str,
    parse_term_nat,
    parse_term_num,
    parse_term_var,
    NULL 
  };

  return parse_choice(s, depth, atoms);
}

fn Term parse_term(PState *s, u32 depth) {
  return parse_term_app(parse_term_atom(s, depth), s, depth);
}
