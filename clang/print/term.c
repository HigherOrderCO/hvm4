fn void print_term_go(FILE *f, Term term, u32 depth);

// Prints APP and DRY chains as f(x,y,z)
fn void print_app(FILE *f, Term term, u32 depth) {
  Term spine[256];
  u32  len  = 0;
  Term curr = term;
  while ((term_tag(curr) == APP || term_tag(curr) == DRY) && len < 256) {
    u32 loc = term_val(curr);
    spine[len++] = HEAP[loc + 1];
    curr = HEAP[loc];
  }
  if (term_tag(curr) == LAM) {
    fputc('(', f);
    print_term_go(f, curr, depth);
    fputc(')', f);
  } else {
    print_term_go(f, curr, depth);
  }
  fputc('(', f);
  for (u32 i = 0; i < len; i++) {
    if (i > 0) {
      fputc(',', f);
    }
    print_term_go(f, spine[len - 1 - i], depth);
  }
  fputc(')', f);
}

fn void print_term_go(FILE *f, Term term, u32 depth) {
  switch (term_tag(term)) {
    case NAM: {
      // Print stuck variable as just the name
      print_name(f, term_ext(term));
      break;
    }
    case DRY: {
      // Print stuck application as f(x,y)
      print_app(f, term, depth);
      break;
    }
    case VAR: {
      print_name(f, term_val(term));
      break;
    }
    case NUM: {
      fprintf(f, "%u", term_val(term));
      break;
    }
    case REF: {
      fputc('@', f);
      print_name(f, term_ext(term));
      break;
    }
    case ERA: {
      fputs("&{}", f);
      break;
    }
    case CO0:
    case CO1: {
      print_name(f, term_val(term));
      fputs(term_tag(term) == CO0 ? "₀" : "₁", f);
      break;
    }
    case LAM: {
      u32 loc = term_val(term);
      u32 nam = depth + 1;
      fputs("λ", f);
      print_name(f, nam);
      fputc('.', f);
      print_term_go(f, HEAP[loc], depth + 1);
      break;
    }
    case APP: {
      print_app(f, term, depth);
      break;
    }
    case SUP: {
      u32 loc = term_val(term);
      fputc('&', f);
      print_name(f, term_ext(term));
      fputc('{', f);
      print_term_go(f, HEAP[loc + 0], depth);
      fputc(',', f);
      print_term_go(f, HEAP[loc + 1], depth);
      fputc('}', f);
      break;
    }
    case DUP: {
      u32 loc = term_val(term);
      u32 nam = depth + 1;
      fputc('!', f);
      print_name(f, nam);
      fputc('&', f);
      print_name(f, term_ext(term));
      fputc('=', f);
      print_term_go(f, HEAP[loc + 0], depth);
      fputc(';', f);
      print_term_go(f, HEAP[loc + 1], depth + 1);
      break;
    }
    case MAT: {
      u32 loc = term_val(term);
      fputs("λ{#", f);
      print_name(f, term_ext(term));
      fputc(':', f);
      print_term_go(f, HEAP[loc + 0], depth);
      fputc(';', f);
      print_term_go(f, HEAP[loc + 1], depth);
      fputc('}', f);
      break;
    }
    case C00 ... C16: {
      u32 ari = term_tag(term) - C00;
      u32 loc = term_val(term);
      u32 nam = term_ext(term);
      fputc('#', f);
      print_name(f, nam);
      fputc('{', f);
      for (u32 i = 0; i < ari; i++) {
        if (i > 0) {
          fputc(',', f);
        }
        print_term_go(f, HEAP[loc + i], depth);
      }
      fputc('}', f);
      break;
    }
    case ALO: {
      fputs("<ALO>", f);
      break;
    }
  }
}

fn void print_term(Term term) {
  print_term_go(stdout, term, 0);
}
