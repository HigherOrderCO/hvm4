// Parse a single atom (no trailing operators or function calls)
fn Term parse_term_atom(PState *s, u32 depth) {
  parse_skip(s);
  u8 c = (u8)parse_peek(s);

  switch (c) {
    case '&':  return parse_term_amp(s, depth);     // &{}, &Lλx{...}, &L{A,B}
    case 0xCE: return parse_term_lambda(s, depth);  // λ (UTF-8: CE BB)
    case '!':  return parse_term_dup(s, depth);     // !x&L=v;body
    case '#':  return parse_term_ctr(s, depth);     // #Name{...}
    case '@':  return parse_term_ref(s, depth);     // @name
    case '^':  return parse_term_nam(s, depth);     // ^name or ^(f x)
    case '(':  return parse_term_par(s, depth);     // (term)
    case '[':  return parse_term_lst(s, depth);     // [a,b,c]
    case '\'': return parse_term_chr(s, depth);     // 'c'
    case '"':  return parse_term_str(s, depth);     // "string"
    default:
      if (isdigit(c)) {
        // Digits: try nat (3n) first, fall back to num (123)
        TermParser alts[] = { parse_term_nat, parse_term_num, NULL };
        return parse_choice(s, depth, alts);
      }
      return parse_term_var(s, depth);
  }
}

fn Term parse_term(PState *s, u32 depth) {
  return parse_term_app(parse_term_atom(s, depth), s, depth);
}
