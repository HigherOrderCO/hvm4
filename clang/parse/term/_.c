// Parse a single atom (no trailing operators or function calls)
fn Term parse_term_atom(PState *s, u32 depth) {
  parse_skip(s);

  return parse_choice(NONE, s, depth, 0, (Parser[]){
    // constants
    parse_term_any, // *
    parse_term_era, // &{} or λ{}

    // λ..
    parse_term_mat, // λ{ctr: .. ; .. [; _:λx.f] }      where [.] means optional and ctr ∈ {#name, 0, 1, .. , 0n, 1n+, [], <>}
    parse_term_use, // λ{f}
    parse_term_lam, // λ[&]x.f or λ[&]x&L.f λ[&]x&(L).f where [&] means optional

    // !..
    parse_term_uns, // !${f, v};body
    parse_term_let, // ![&]x = val or !![&]x =val
    parse_term_dup, // ![&]x&[L] = v; f or ![&]x&(L) = v; f

    // &..
    parse_term_frk, // &Lλx,y{A[x,y];B[x,y]} or &Lλx,y{&₀: A[x,y]; &₁: B[x,y]}
    parse_term_sup, // &L{A,B} or &(L){A,B}

    // unique prefix
    parse_term_ctr, // #name or #name{} or #name{a,b..}
    parse_term_ref, // @f
    parse_term_nam, // ^name
    parse_term_par, // (term)
    parse_term_lst, // [1,2,3]
    parse_term_chr, // 'c'
    parse_term_str, // "string"
    parse_term_nat, // 0n, 1n..
    parse_term_num, // 0 , 1..
    parse_term_var, // name
    NULL
  });

}

fn Term parse_term(PState *s, u32 depth) {
  return parse_term_app(parse_term_atom(s, depth), s, depth);
}
