fn Term wnf(Term term) {
  S_POS = 0;
  Term next = term;
  Term whnf;

  enter: {
    if (DEBUG) {
      printf("wnf_enter: ");
      print_term(next);
      printf("\n");
    }

    switch (term_tag(next)) {
      case VAR: {
        u32 loc = term_val(next);
        if (term_sub(HEAP[loc])) {
          next = term_unmark(HEAP[loc]);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case CO0:
      case CO1: {
        u32 loc = term_val(next);
        if (term_sub(HEAP[loc])) {
          next = term_unmark(HEAP[loc]);
          goto enter;
        }
        Term dup_val = HEAP[loc];
        STACK[S_POS++] = next;
        next = dup_val;
        goto enter;
      }

      case APP: {
        u32  loc = term_val(next);
        Term fun = HEAP[loc];
        STACK[S_POS++] = next;
        next = fun;
        goto enter;
      }

      case DUP: {
        u32  loc  = term_val(next);
        Term body = HEAP[loc + 1];
        next = body;
        goto enter;
      }

      case REF: {
        u32 nam = term_ext(next);
        if (BOOK[nam] != 0) {
          u64 alo_loc = heap_alloc(1);
          HEAP[alo_loc] = (u64)BOOK[nam];
          next = term_new(0, ALO, 0, alo_loc);
          goto enter;
        }
        whnf = next;
        goto apply;
      }

      case ALO: {
        u32  alo_loc = term_val(next);
        u64  pair    = HEAP[alo_loc];
        u32  tm_loc  = (u32)(pair & 0xFFFFFFFF);
        u32  ls_loc  = (u32)(pair >> 32);
        Term book    = HEAP[tm_loc];

        switch (term_tag(book)) {
          case VAR: {
            next = wnf_alo_var(ls_loc, term_val(book));
            goto enter;
          }
          case CO0:
          case CO1: {
            next = wnf_alo_cop(ls_loc, term_val(book), term_ext(book), term_tag(book) == CO0 ? 0 : 1);
            goto enter;
          }
          case NAM: {
            next = wnf_alo_nam(term_ext(book));
            goto enter;
          }
          case DRY: {
            next = wnf_alo_dry(ls_loc, term_val(book));
            goto enter;
          }
          case LAM: {
            next = wnf_alo_lam(ls_loc, term_val(book));
            goto enter;
          }
          case APP:
          case SUP:
          case MAT:
          case C00 ... C16: {
            next = wnf_alo_node(ls_loc, term_val(book), term_tag(book), term_ext(book), term_arity(book));
            goto enter;
          }
          case DUP: {
            next = wnf_alo_dup(ls_loc, term_val(book), term_ext(book));
            goto enter;
          }
          case NUM: {
            next = term_new_num(term_val(book));
            goto enter;
          }
          case REF:
          case ERA: {
            next = book;
            goto enter;
          }
        }
      }

      case NAM:
      case DRY:
      case ERA:
      case SUP:
      case LAM:
      case NUM:
      case MAT:
      case C00 ... C16: {
        whnf = next;
        goto apply;
      }

      default: {
        whnf = next;
        goto apply;
      }
    }
  }

  apply: {
    if (DEBUG) {
      printf("wnf_apply: ");
      print_term(whnf);
      printf("\n");
    }

    while (S_POS > 0) {
      Term frame = STACK[--S_POS];

      switch (term_tag(frame)) {
        case APP: {
          u32  loc = term_val(frame);
          Term arg = HEAP[loc + 1];

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_app_era();
              continue;
            }
            case NAM: {
              whnf = wnf_app_nam(whnf, arg);
              continue;
            }
            case DRY: {
              whnf = wnf_app_dry(whnf, arg);
              continue;
            }
            case LAM: {
              whnf = wnf_app_lam(whnf, arg);
              next = whnf;
              goto enter;
            }
            case SUP: {
              whnf = wnf_app_sup(frame, whnf);
              next = whnf;
              goto enter;
            }
            case MAT: {
              STACK[S_POS++] = whnf;
              next = arg;
              goto enter;
            }
            case C00 ... C16: {
              whnf = wnf_app_ctr(whnf, arg);
              continue;
            }
            default: {
              whnf = term_new_app(whnf, arg);
              continue;
            }
          }
        }

        case MAT: {
          Term mat = frame;
          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_app_era();
              continue;
            }
            case SUP: {
              whnf = wnf_app_mat_sup(mat, whnf);
              next = whnf;
              goto enter;
            }
            case C00 ... C16: {
              whnf = wnf_app_mat_ctr(mat, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              whnf = term_new_app(mat, whnf);
              continue;
            }
          }
        }

        case CO0:
        case CO1: {
          u8  side = (term_tag(frame) == CO0) ? 0 : 1;
          u32 loc  = term_val(frame);
          u32 lab  = term_ext(frame);

          switch (term_tag(whnf)) {
            case NAM: {
              whnf = wnf_dup_nam(lab, loc, side, whnf);
              continue;
            }
            case DRY: {
              whnf = wnf_dup_dry(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case LAM: {
              whnf = wnf_dup_lam(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case SUP: {
              whnf = wnf_dup_sup(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            case ERA:
            case NUM: {
              whnf = wnf_dup_node(lab, loc, side, whnf);
              continue;
            }
            case MAT:
            case C00 ... C16: {
              whnf = wnf_dup_node(lab, loc, side, whnf);
              next = whnf;
              goto enter;
            }
            default: {
              u64 new_loc   = heap_alloc(1);
              HEAP[new_loc] = whnf;
              heap_subst_var(loc, term_new(0, side == 0 ? CO1 : CO0, lab, new_loc));
              whnf          = term_new(0, side == 0 ? CO0 : CO1, lab, new_loc);
              continue;
            }
          }
        }

        default: {
          continue;
        }
      }
    }
  }

  return whnf;
}
