// Collapse step: recursively searches for SUPs and lifts them to the top level.
// Uses direct SUP lifting for efficiency.
// Stops when it finds a SUP at the top (doesn't descend into SUP branches).
// Also strips RED nodes (keeping only RHS) and propagates ERA upward.
// Used by flatten() for lazy BFS enumeration of superposition branches.
//
// IMPORTANT: When a SUP is found and lifted, we return immediately WITHOUT
// recursively collapsing the new branches. This is critical for handling
// infinite structures - flatten() will iterate lazily via BFS.

fn Term collapse_step(Term term);

// Optimized collapse step with UNDUP optimization.
// Traverses PARENT chain to find SUPs with ERA siblings, sets UNDUP,
// calls collapse_step, then clears UNDUP by traversing again.
fn Term collapse_step_opt(u32 loc) {
  // Traverse PARENT chain and mark UNDUP for SUPs with ERA siblings
  u32 cur = loc;
  while (cur != 0 && PARENT[cur] != 0) {
    u32 parent_loc = PARENT[cur];
    Term parent = HEAP[parent_loc];

    if (term_tag(parent) == SUP) {
      u32 sup_loc = term_val(parent);
      u32 lab = term_ext(parent);

      if (cur == sup_loc + 0 && term_tag(HEAP[sup_loc + 1]) == ERA) {
        UNDUP[lab] = UNDUP_1;
      } else if (cur == sup_loc + 1 && term_tag(HEAP[sup_loc + 0]) == ERA) {
        UNDUP[lab] = UNDUP_0;
      }
    }

    cur = parent_loc;
  }

  Term result = collapse_step(HEAP[loc]);

  // Clear UNDUP by traversing again
  cur = loc;
  while (cur != 0 && PARENT[cur] != 0) {
    u32 parent_loc = PARENT[cur];
    Term parent = HEAP[parent_loc];

    if (term_tag(parent) == SUP) {
      u32 sup_loc = term_val(parent);
      u32 lab = term_ext(parent);

      if (term_tag(HEAP[sup_loc + 0]) == ERA || term_tag(HEAP[sup_loc + 1]) == ERA) {
        UNDUP[lab] = 0;
      }
    }

    cur = parent_loc;
  }

  return result;
}

fn Term collapse_step(Term term) {
  term = wnf(term);

  switch (term_tag(term)) {
    case ERA:
    case VAR:
    case REF:
    case NUM:
    case CO0:
    case CO1:
    case NAM: {
      return term;
    }

    case SUP: {
      u32 lab = term_ext(term);
      u32 loc = term_val(term);
      // UNDUP: if this SUP has UNDUP set, return the live side
      if (UNDUP && UNDUP[lab]) {
        if (UNDUP[lab] == UNDUP_0) {
          return collapse_step(HEAP[loc + 1]); // Skip side 0
        } else {
          return collapse_step(HEAP[loc + 0]); // Skip side 1
        }
      }
      // Found a SUP - return it for flatten to handle
      return term;
    }

    case INC: {
      u64  loc = term_val(term);
      Term chi = collapse_step(HEAP[loc]);
      HEAP[loc] = chi;
      if (term_tag(chi) == ERA) {
        return term_new_era();
      }
      return term;
    }

    case RED: {
      // For RED, collapse the rhs (g) side only
      u64 loc = term_val(term);
      return collapse_step(HEAP[loc + 1]);
    }

    case LAM: {
      u64  lam_loc = term_val(term);
      Term body    = HEAP[lam_loc];

      // Recursively collapse the body to find SUPs
      Term body_collapsed = collapse_step(body);
      HEAP[lam_loc] = body_collapsed;

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
      Term sup_a   = HEAP[sup_loc + 0];
      Term sup_b   = HEAP[sup_loc + 1];

      // Allocate: 2 lambda bodies (for fresh binders)
      u64 loc0 = heap_alloc(1);
      u64 loc1 = heap_alloc(1);

      // Put SUP branches in new lambda bodies
      HEAP[loc0] = sup_a;
      HEAP[loc1] = sup_b;

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
        children[i] = collapse_step(HEAP[loc + i]);
        HEAP[loc + i] = children[i];

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
      Term sup_a   = HEAP[sup_loc + 0];
      Term sup_b   = HEAP[sup_loc + 1];

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
