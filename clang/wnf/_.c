fn Term wnf(Term term) {
  u32 base = S_POS;
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
//          case SWI:
//          case USE:
          case C00 ... C16: {
//          case P00 ... P16: {
            u32 ari = (term_tag(book) >= P00) ? (term_tag(book) - P00) : term_arity(book);
            next = wnf_alo_node(ls_loc, term_val(book), term_tag(book), term_ext(book), ari);
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

//      case P00 ... P16: {
//        // Call the primitive directly (it handles strict evaluation internally)
//        u32  nam = term_ext(next);
//        u32  ari = term_tag(next) - P00;
//        u32  loc = term_val(next);
//        ITRS++;
//        next = prim_call(nam, ari, loc);
//        goto enter;
//      }

      case NAM:
      case DRY:
      case ERA:
      case SUP:
      case LAM:
      case NUM:
      case MAT:
//      case SWI:
//      case USE:
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
//            case SWI: {
//              STACK[S_POS++] = whnf;
//              next = arg;
//              goto enter;
//            }
//            case USE: {
//              STACK[S_POS++] = whnf;
//              next = arg;
//              goto enter;
//            }
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

//        case SWI: {
//          // λ{num: f; g} applied to whnf
//          // If whnf == num, return f; else return (g whnf)
//          u32  num = term_ext(frame);
//          u32  loc = term_val(frame);
//          Term f   = HEAP[loc + 0];
//          Term g   = HEAP[loc + 1];
//          switch (term_tag(whnf)) {
//            case ERA: {
//              whnf = wnf_app_era();
//              continue;
//            }
//            case NUM: {
//              ITRS++;
//              if (term_val(whnf) == num) {
//                next = f;
//              } else {
//                next = term_new_app(g, whnf);
//              }
//              goto enter;
//            }
//            case SUP: {
//              // Clone SWI and distribute over SUP
//              u32  lab     = term_ext(whnf);
//              u32  sup_loc = term_val(whnf);
//              Copy F       = term_clone(lab, f);
//              Copy G       = term_clone(lab, g);
//              Term swi0    = term_new_swi(num, F.k0, G.k0);
//              Term swi1    = term_new_swi(num, F.k1, G.k1);
//              Term app0    = term_new_app(swi0, HEAP[sup_loc + 0]);
//              Term app1    = term_new_app(swi1, HEAP[sup_loc + 1]);
//              ITRS++;
//              next = term_new_sup(lab, app0, app1);
//              goto enter;
//            }
//            default: {
//              whnf = term_new_app(frame, whnf);
//              continue;
//            }
//          }
//        }
//
//        case USE: {
//          // λ{f} applied to whnf - just apply f to whnf
//          u32  loc = term_val(frame);
//          Term f   = HEAP[loc];
//          switch (term_tag(whnf)) {
//            case ERA: {
//              whnf = wnf_app_era();
//              continue;
//            }
//            case SUP: {
//              // Clone f and distribute over SUP
//              u32  lab     = term_ext(whnf);
//              u32  sup_loc = term_val(whnf);
//              Copy F       = term_clone(lab, f);
//              Term use0    = term_new_use(F.k0);
//              Term use1    = term_new_use(F.k1);
//              Term app0    = term_new_app(use0, HEAP[sup_loc + 0]);
//              Term app1    = term_new_app(use1, HEAP[sup_loc + 1]);
//              ITRS++;
//              next = term_new_sup(lab, app0, app1);
//              goto enter;
//            }
//            default: {
//              // Apply f to whnf
//              ITRS++;
//              next = term_new_app(f, whnf);
//              goto enter;
//            }
//          }
//        }

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
//            case SWI:
//            case USE:
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
