// Collapse step: recursively searches for SUPs and lifts them to the top level.
// Uses direct SUP lifting for efficiency.
// Stops when it finds a SUP at the top (doesn't descend into SUP branches).
// Also strips RED nodes (keeping only RHS) and propagates ERA upward.
// Used by collapse_flatten() for lazy BFS enumeration of superposition branches.
//
// IMPORTANT: When a SUP is found and lifted, we return immediately WITHOUT
// recursively collapsing the new branches. This is critical for handling
// infinite structures - collapse_flatten() will iterate lazily via BFS.

fn Term collapse_step(Term term) {
  term = wnf(term);

  switch (term_tag(term)) {
    case ERA:
    case VAR:
    case REF:
    case NUM:
    case DP0:
    case DP1:
    case NAM:
    case BJV:
    case BJ0:
    case BJ1: {
      return term;
    }

    case SUP: {
      // Found a SUP - return it immediately, don't descend into branches
      return term;
    }

    case INC: {
      // INC: just return as-is, let collapse_flatten() handle the priority adjustment
      // Don't lift SUPs through INCs here - that's handled by the collapse_flatten loop
      return term;
    }

    case RED: {
      // For RED, collapse the rhs (g) side only
      u64 loc = term_val(term);
      return collapse_step(heap_get(loc + 1));
    }

    case LAM: {
      u64  lam_loc = term_val(term);
      Term body    = heap_get(lam_loc);

      // Recursively collapse the body to find SUPs
      Term body_collapsed = collapse_step(body);
      heap_set(lam_loc, body_collapsed);

      // ERA propagation: if body is ERA, whole lambda is ERA
      if (term_tag(body_collapsed) == ERA) {
        return term_new_era();
      }

      if (term_tag(body_collapsed) != SUP) {
        // No SUP found in body - return the LAM unchanged
        return term;
      }

      // SUP in body - lift it: λx. &L{a, b} → &L{λx.a, λx.b}
      // We need to handle variable binding correctly using dup_lam pattern
      u32  lab     = term_ext(body_collapsed);
      u64  sup_loc = term_val(body_collapsed);
      Term sup_a   = heap_get(sup_loc + 0);
      Term sup_b   = heap_get(sup_loc + 1);

      // Allocate: 2 lambda bodies (for fresh binders)
      u64 loc0 = heap_alloc(1);
      u64 loc1 = heap_alloc(1);

      // Put SUP branches in new lambda bodies
      heap_set(loc0, sup_a);
      heap_set(loc1, sup_b);

      // Create SUP of variables for the original binder
      // Any reference to lam_loc will be substituted with this SUP
      Term var0 = term_new_var(loc0);
      Term var1 = term_new_var(loc1);
      Term binder_sup = term_new_sup(lab, var0, var1);

      // Substitute original binder with SUP of new variables
      heap_subst_var(lam_loc, binder_sup);

      // Create two lambdas with fresh binders - DON'T recursively collapse!
      Term lam0 = term_new(0, LAM, 0, loc0);
      Term lam1 = term_new(0, LAM, 0, loc1);

      return term_new_sup(lab, lam0, lam1);
    }

    default: {
      // Generic case for APP, MAT, CTR, OP2, USE, etc.
      u32 ari = term_arity(term);
      u64 loc = term_val(term);

      if (ari == 0) {
        return term;
      }

      // First pass: collapse all children and check for SUPs/ERAs
      int  sup_idx = -1;  // Index of first SUP child (-1 if none)
      Term children[16];

      for (u32 i = 0; i < ari; i++) {
        children[i] = collapse_step(heap_get(loc + i));
        heap_set(loc + i, children[i]);

        // ERA propagation: if any child is ERA, whole node is ERA
        if (term_tag(children[i]) == ERA) {
          return term_new_era();
        }

        // Track first SUP
        if (sup_idx < 0 && term_tag(children[i]) == SUP) {
          sup_idx = i;
        }
      }

      if (sup_idx < 0) {
        // No SUPs found - term is fully collapsed
        return term;
      }

      // Found SUP at index sup_idx - lift it directly
      // T(..., &L{a,b}, ...) → &L{T(...,a,...), T(...,b,...)}
      Term sup     = children[sup_idx];
      u32  lab     = term_ext(sup);
      u64  sup_loc = term_val(sup);
      Term sup_a   = heap_get(sup_loc + 0);
      Term sup_b   = heap_get(sup_loc + 1);

      // Build two versions of the node
      Term args0[16], args1[16];

      for (u32 i = 0; i < ari; i++) {
        if ((int)i == sup_idx) {
          // This is the SUP position - substitute branches directly
          args0[i] = sup_a;
          args1[i] = sup_b;
        } else {
          // Clone other children with the SUP's label
          Copy c = term_clone(lab, children[i]);
          args0[i] = c.k0;
          args1[i] = c.k1;
        }
      }

      // DON'T recursively collapse - just build the nodes and return SUP
      // flatten() will iterate lazily
      Term node0 = term_new_(term_tag(term), term_ext(term), ari, args0);
      Term node1 = term_new_(term_tag(term), term_ext(term), ari, args1);

      return term_new_sup(lab, node0, node1);
    }
  }
}
