__attribute__((hot)) fn Term wnf(Term term) {
  u32 base = S_POS;
  Term next = term;
  Term whnf;

  enter: {
    if (__builtin_expect(DEBUG, 0)) {
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

      case UNS: {
        next = wnf_uns(next);
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
          case SWI:
          case USE:
          case UNS:
          case C00 ... C16:
          case OP2:
          case EQL:
          case DSU:
          case DDU:
          case RED: {
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

      case OP2: {
        u32  loc = term_val(next);
        Term x   = HEAP[loc + 0];
        STACK[S_POS++] = next;
        next = x;
        goto enter;
      }

      case EQL: {
        u32  loc = term_val(next);
        Term a   = HEAP[loc + 0];
        STACK[S_POS++] = next;
        next = a;
        goto enter;
      }

      case DSU: {
        u32  loc = term_val(next);
        Term lab = HEAP[loc + 0];
        STACK[S_POS++] = next;
        next = lab;
        goto enter;
      }

      case DDU: {
        u32  loc = term_val(next);
        Term lab = HEAP[loc + 0];
        STACK[S_POS++] = next;
        next = lab;
        goto enter;
      }

      case RED:
      case NAM:
      case DRY:
      case ERA:
      case SUP:
      case LAM:
      case NUM:
      case MAT:
      case SWI:
      case USE:
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
    if (__builtin_expect(DEBUG, 0)) {
      printf("wnf_apply: ");
      print_term(whnf);
      printf("\n");
    }

    while (S_POS > base) {
      Term frame = STACK[--S_POS];

      switch (term_tag(frame)) {
        // -----------------------------------------------------------------------
        // APP frame: (□ x) - we reduced func, now dispatch
        // -----------------------------------------------------------------------
        case APP: {
          u32  app_loc = term_val(frame);
          Term arg     = HEAP[app_loc + 1];

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
              next = wnf_app_lam(whnf, arg);
              goto enter;
            }
            case SUP: {
              next = wnf_app_sup(frame, whnf);
              goto enter;
            }
            case MAT:
            case SWI: {
              STACK[S_POS++] = whnf;
              next = arg;
              goto enter;
            }
            case USE: {
              STACK[S_POS++] = whnf;
              next = arg;
              goto enter;
            }
            case RED: {
              // ((f ~> g) x): write RED to heap, push F_APP_RED(app_loc), enter g
              HEAP[app_loc + 0] = whnf;  // update heap so F_APP_RED can read it
              u32  red_loc = term_val(whnf);
              Term g       = HEAP[red_loc + 1];
              STACK[S_POS++] = term_new(0, F_APP_RED, 0, app_loc);
              next = g;
              goto enter;
            }
            default: {
              whnf = term_new_app(whnf, arg);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // F_APP_RED frame: ((f ~> □) x) - we reduced g, now dispatch on g
        // -----------------------------------------------------------------------
        case F_APP_RED: {
          u32  app_loc = term_val(frame);
          Term red     = HEAP[app_loc + 0];
          u32  red_loc = term_val(red);
          Term f       = HEAP[red_loc + 0];
          Term arg     = HEAP[app_loc + 1];
          Term g       = whnf;

          switch (term_tag(g)) {
            case ERA: {
              next = wnf_app_red_era();
              goto enter;
            }
            case SUP: {
              next = wnf_app_red_sup(f, g, arg);
              goto enter;
            }
            case LAM: {
              next = wnf_app_red_lam(f, g, arg);
              goto enter;
            }
            case RED: {
              next = wnf_app_red_red(f, g, arg);
              goto enter;
            }
            case MAT:
            case SWI: {
              // ((f ~> mat) x): store mat in RED's g slot, push F_RED_MAT, enter arg
              HEAP[red_loc + 1] = g;  // store mat where g was
              STACK[S_POS++] = term_new(0, F_RED_MAT, 0, app_loc);
              next = arg;
              goto enter;
            }
            case USE: {
              // ((f ~> use) x): store use in RED's g slot, push F_RED_USE, enter arg
              HEAP[red_loc + 1] = g;
              STACK[S_POS++] = term_new(0, F_RED_USE, 0, app_loc);
              next = arg;
              goto enter;
            }
            case NAM: {
              whnf = wnf_app_red_nam(f, g, arg);
              continue;
            }
            case DRY: {
              whnf = wnf_app_red_dry(f, g, arg);
              continue;
            }
            case C00 ... C16: {
              whnf = wnf_app_red_ctr(f, g, arg);
              continue;
            }
            default: {
              whnf = term_new_app(term_new_red(f, g), arg);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // MAT/SWI frame: (mat □) - we reduced arg, dispatch mat interaction
        // -----------------------------------------------------------------------
        case MAT:
        case SWI: {
          Term mat = frame;
          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_app_era();
              continue;
            }
            case SUP: {
              next = wnf_app_mat_sup(mat, whnf);
              goto enter;
            }
            case C00 ... C16: {
              next = wnf_app_mat_ctr(mat, whnf);
              goto enter;
            }
            case NUM: {
              // (mat #n): compare ext(mat) to val(num)
              ITRS++;
              u32  loc = term_val(mat);
              Term f   = HEAP[loc + 0];
              Term g   = HEAP[loc + 1];
              if (term_ext(mat) == term_val(whnf)) {
                next = f;
              } else {
                next = term_new_app(g, whnf);
              }
              goto enter;
            }
            case RED: {
              // (mat (g ~> h)): drop g, reduce (mat h)
              u32  red_loc = term_val(whnf);
              Term h = HEAP[red_loc + 1];
              STACK[S_POS++] = mat;
              next = h;
              goto enter;
            }
            default: {
              whnf = term_new_app(mat, whnf);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // F_RED_MAT frame: ((f ~> mat) □) - we reduced arg, dispatch guarded mat
        // -----------------------------------------------------------------------
        case F_RED_MAT: {
          u32  app_loc = term_val(frame);
          Term red     = HEAP[app_loc + 0];
          u32  red_loc = term_val(red);
          Term f       = HEAP[red_loc + 0];
          Term mat     = HEAP[red_loc + 1];  // mat was stored here
          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_app_red_mat_era();
              continue;
            }
            case SUP: {
              next = wnf_app_red_mat_sup(f, mat, whnf);
              goto enter;
            }
            case C00 ... C16: {
              if (term_ext(mat) == term_ext(whnf)) {
                next = wnf_app_red_mat_ctr_match(f, mat, whnf);
              } else {
                next = wnf_app_red_mat_ctr_miss(f, mat, whnf);
              }
              goto enter;
            }
            case NUM: {
              if (term_ext(mat) == term_val(whnf)) {
                next = wnf_app_red_mat_num_match(f, mat, whnf);
              } else {
                next = wnf_app_red_mat_num_miss(f, mat, whnf);
              }
              goto enter;
            }
            case RED: {
              // ((f ~> mat) (g ~> h)): drop g, reduce (mat h) in guarded context
              u32  arg_red_loc = term_val(whnf);
              Term h = HEAP[arg_red_loc + 1];
              STACK[S_POS++] = frame;  // keep F_RED_MAT frame
              next = h;
              goto enter;
            }
            default: {
              // Stuck - drop g, return ^(f arg)
              whnf = term_new_dry(f, whnf);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // USE frame: (use □) - we reduced arg, dispatch use interaction
        // -----------------------------------------------------------------------
        case USE: {
          Term use = frame;
          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_use_era();
              continue;
            }
            case SUP: {
              next = wnf_use_sup(use, whnf);
              goto enter;
            }
            case RED: {
              // (use (g ~> h)): drop g, reduce (use h)
              u32  red_loc = term_val(whnf);
              Term h = HEAP[red_loc + 1];
              STACK[S_POS++] = use;
              next = h;
              goto enter;
            }
            default: {
              next = wnf_use_val(use, whnf);
              goto enter;
            }
          }
        }

        // -----------------------------------------------------------------------
        // F_RED_USE frame: ((f ~> use) □) - we reduced arg, dispatch guarded use
        // -----------------------------------------------------------------------
        case F_RED_USE: {
          u32  app_loc = term_val(frame);
          Term red     = HEAP[app_loc + 0];
          u32  red_loc = term_val(red);
          Term f       = HEAP[red_loc + 0];
          Term use     = HEAP[red_loc + 1];  // use was stored here
          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_app_red_use_era();
              continue;
            }
            case SUP: {
              next = wnf_app_red_use_sup(f, use, whnf);
              goto enter;
            }
            case RED: {
              // ((f ~> use) (g ~> h)): drop g, reduce (use h) in guarded context
              u32  arg_red_loc = term_val(whnf);
              Term h = HEAP[arg_red_loc + 1];
              STACK[S_POS++] = frame;  // keep F_RED_USE frame
              next = h;
              goto enter;
            }
            case NAM:
            case DRY: {
              // Stuck - drop g, return ^(f arg)
              whnf = term_new_dry(f, whnf);
              continue;
            }
            default: {
              next = wnf_app_red_use_val(f, use, whnf);
              goto enter;
            }
          }
        }

        // -----------------------------------------------------------------------
        // CO0/CO1 frame: dup - we reduced the value, dispatch dup interaction
        // -----------------------------------------------------------------------
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
              next = wnf_dup_dry(lab, loc, side, whnf);
              goto enter;
            }
            case RED: {
              next = wnf_dup_red(lab, loc, side, whnf);
              goto enter;
            }
            case LAM: {
              next = wnf_dup_lam(lab, loc, side, whnf);
              goto enter;
            }
            case SUP: {
              next = wnf_dup_sup(lab, loc, side, whnf);
              goto enter;
            }
            case ERA:
            case NUM: {
              whnf = wnf_dup_node(lab, loc, side, whnf);
              continue;
            }
            case MAT:
            case SWI:
            case USE:
            case OP2:
            case DSU:
            case DDU:
            case C00 ... C16: {
              next = wnf_dup_node(lab, loc, side, whnf);
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

        // -----------------------------------------------------------------------
        // OP2 frame: (□ op y) - we reduced x, dispatch or transition to F_OP2_NUM
        // -----------------------------------------------------------------------
        case OP2: {
          u32  opr = term_ext(frame);
          u32  loc = term_val(frame);
          Term y   = HEAP[loc + 1];

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_op2_era();
              continue;
            }
            case NUM: {
              // x is NUM, now reduce y: push F_OP2_NUM frame
              STACK[S_POS++] = term_new(0, F_OP2_NUM, opr, term_val(whnf));
              next = y;
              goto enter;
            }
            case SUP: {
              next = wnf_op2_sup(opr, whnf, y);
              goto enter;
            }
            default: {
              whnf = term_new_op2(opr, whnf, y);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // F_OP2_NUM frame: (x op □) - x is NUM, we reduced y, dispatch
        // -----------------------------------------------------------------------
        case F_OP2_NUM: {
          u32 opr   = term_ext(frame);
          u32 x_val = term_val(frame);
          Term x    = term_new_num(x_val);

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_op2_num_era();
              continue;
            }
            case NUM: {
              whnf = wnf_op2_num_num(opr, x, whnf);
              continue;
            }
            case SUP: {
              next = wnf_op2_num_sup(opr, x, whnf);
              goto enter;
            }
            case RED: {
              // (x op (f ~> g)): drop f, reduce (x op g)
              u32  red_loc = term_val(whnf);
              Term g = HEAP[red_loc + 1];
              STACK[S_POS++] = frame;
              next = g;
              goto enter;
            }
            default: {
              // Stuck: (x op y) where x is NUM, y is not
              whnf = term_new_op2(opr, x, whnf);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // EQL frame: (□ === b) - we reduced a, transition to F_EQL_R or dispatch
        // -----------------------------------------------------------------------
        case EQL: {
          u32  loc = term_val(frame);
          Term b   = HEAP[loc + 1];

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_eql_era_l();
              continue;
            }
            case SUP: {
              next = wnf_eql_sup_l(whnf, b);
              goto enter;
            }
            default: {
              // Store a's WHNF location, push F_EQL_R, enter b
              // We store a in HEAP[loc+0] for later retrieval
              HEAP[loc + 0] = whnf;
              STACK[S_POS++] = term_new(0, F_EQL_R, 0, loc);
              next = b;
              goto enter;
            }
          }
        }

        // -----------------------------------------------------------------------
        // F_EQL_R frame: (a === □) - we reduced b, now compare both WHNFs
        // -----------------------------------------------------------------------
        case F_EQL_R: {
          u32  loc = term_val(frame);
          Term a   = HEAP[loc + 0];  // a's WHNF was stored here

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_eql_era_r();
              continue;
            }
            case SUP: {
              next = wnf_eql_sup_r(a, whnf);
              goto enter;
            }
            default: {
              // Both a and b are WHNF, now dispatch based on types
              u8 a_tag = term_tag(a);
              u8 b_tag = term_tag(whnf);

              // NUM === NUM
              if (a_tag == NUM && b_tag == NUM) {
                whnf = wnf_eql_num(a, whnf);
                continue;
              }
              // LAM === LAM
              if (a_tag == LAM && b_tag == LAM) {
                next = wnf_eql_lam(a, whnf);
                goto enter;
              }
              // CTR === CTR
              if (a_tag >= C00 && a_tag <= C16 && b_tag >= C00 && b_tag <= C16) {
                next = wnf_eql_ctr(a, whnf);
                goto enter;
              }
              // MAT/SWI === MAT/SWI
              if ((a_tag == MAT || a_tag == SWI) && (b_tag == MAT || b_tag == SWI)) {
                next = wnf_eql_mat(a, whnf);
                goto enter;
              }
              // USE === USE
              if (a_tag == USE && b_tag == USE) {
                next = wnf_eql_use(a, whnf);
                goto enter;
              }
              // NAM === NAM
              if (a_tag == NAM && b_tag == NAM) {
                whnf = wnf_eql_nam(a, whnf);
                continue;
              }
              // DRY === DRY
              if (a_tag == DRY && b_tag == DRY) {
                next = wnf_eql_dry(a, whnf);
                goto enter;
              }
              // Otherwise: not equal
              ITRS++;
              whnf = term_new_num(0);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // DSU frame: &(□){a,b} - we reduced lab, dispatch
        // -----------------------------------------------------------------------
        case DSU: {
          u32  loc = term_val(frame);
          Term a   = HEAP[loc + 1];
          Term b   = HEAP[loc + 2];

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_dsu_era();
              continue;
            }
            case NUM: {
              next = wnf_dsu_num(whnf, a, b);
              goto enter;
            }
            case SUP: {
              next = wnf_dsu_sup(whnf, a, b);
              goto enter;
            }
            default: {
              whnf = term_new_dsu(whnf, a, b);
              continue;
            }
          }
        }

        // -----------------------------------------------------------------------
        // DDU frame: ! x &(□) = val; bod - we reduced lab, dispatch
        // -----------------------------------------------------------------------
        case DDU: {
          u32  loc = term_val(frame);
          Term val = HEAP[loc + 1];
          Term bod = HEAP[loc + 2];

          switch (term_tag(whnf)) {
            case ERA: {
              whnf = wnf_ddu_era();
              continue;
            }
            case NUM: {
              next = wnf_ddu_num(whnf, val, bod);
              goto enter;
            }
            case SUP: {
              next = wnf_ddu_sup(whnf, val, bod);
              goto enter;
            }
            default: {
              whnf = term_new_ddu(whnf, val, bod);
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
