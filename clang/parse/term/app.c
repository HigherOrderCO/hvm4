fn Term parse_term(PState *s, u32 depth);
fn Term parse_term_atom(PState *s, u32 depth);
fn int parse_term_opr_peek(PState *s);
fn void parse_term_opr_consume(PState *s, int op);
fn int parse_term_opr_prec(int op);

fn Term parse_term_app_prec(Term f, PState *s, u32 depth, int min_prec);

fn Term parse_term_app(Term f, PState *s, u32 depth) {
  return parse_term_app_prec(f, s, depth, 0);
}

fn Term parse_term_app_prec(Term f, PState *s, u32 depth, int min_prec) {
  return parse_choice(f, s, depth, min_prec, (Parser[]){
    parse_postfix_red,   // ~>
    parse_postfix_cons,  // <>
    parse_postfix_eql,   // === (must be before opr which has ==)
    parse_postfix_and,   // .&.
    parse_postfix_or,    // .|.
    parse_postfix_opr,   // + - * / == != etc.
    parse_postfix_call,  // f(args)
    NULL
  });
}
