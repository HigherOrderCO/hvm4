fn u32 term_arity(Term t) {
  switch (term_tag(t)) {
    case NAM: {
      return 0;
    }
    case LAM: {
      return 1;
    }
    case APP:
    case SUP:
    case DUP:
    case MAT:
    case DRY: {
      return 2;
    }
    case NUM: {
      return 0;
    }
    case C00 ... C16: {
      return term_tag(t) - C00;
    }
    default: {
      return 0;
    }
  }
}
