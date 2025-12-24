fn Term collapse(Term term);

fn Term collapse_inject(Term template, Term *args, u32 n_args) {
  if (n_args == 0) {
    return template;
  }

  Term head = wnf(args[0]);

  if (term_tag(head) == SUP) {
    u32  lab     = term_ext(head);
    u64  sup_loc = term_val(head);
    Term sup_a   = heap_get(sup_loc + 0);
    Term sup_b   = heap_get(sup_loc + 1);

    Copy T = term_clone(lab, template);
    Term args0[16], args1[16];
    args0[0] = sup_a;
    args1[0] = sup_b;
    term_clone_many(lab, args + 1, n_args - 1, args0 + 1, args1 + 1);

    Term r0 = collapse_inject(T.k0, args0, n_args);
    Term r1 = collapse_inject(T.k1, args1, n_args);

    return term_new_sup(lab, r0, r1);
  } else {
    Term applied = term_new_app(template, head);
    return collapse_inject(applied, args + 1, n_args - 1);
  }
}
