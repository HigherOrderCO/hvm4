fn u32 term_arity(Term t) {
  switch (term_tag(t)) {
    case NAM: {
      return 0;
    }
    case BJV:
    case BJ0:
    case BJ1: {
      return 0;
    }
    case LAM: {
      return 1;
    }
    case APP:
    case SUP:
    case DUP:
    case MAT:
    case SWI:
    case DRY:
    case RED: {
      return 2;
    }
    case USE: {
      return 1;
    }
    case NUM: {
      return 0;
    }
    case C00 ... C16: {
      return term_tag(t) - C00;
    }
    case OP2:
    case EQL:
    case AND:
    case OR: {
      return 2;
    }
    case DSU:
    case DDU: {
      return 3;
    }
    case UNS: {
      return 1;
    }
    case INC: {
      return 1;
    }
    default: {
      return 0;
    }
  }
}
