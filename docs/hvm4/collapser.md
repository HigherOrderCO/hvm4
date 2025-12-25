# Collapser (CNF Readback)

Interaction Calculus is affine and uses explicit duplication (DUP) and
superposition (SUP). That is great for optimal sharing but hard for humans to
read. The collapser is the readback procedure: it turns one IC term into a
stream of ordinary lambda terms, i.e., collapsed normal form (CNF).

Two insights make this possible:
- Quoting removes DUPs. When a branch is ready to print, we run `snf(term)` and
  print in quoted mode. Lambdas substitute their binders to BJV during printing,
  so linked vars render as quoted vars (BJV/BJ0/BJ1). DUP interactions are
  defined on quoted dup vars, so DUP nodes are cloned away and disappear from
  the printed term.
- Lifting removes SUPs. We lift the first SUP to the top and enumerate its
  branches. Same-label SUPs annihilate pairwise; different-label SUPs commute and
  create a cross product of branches.

## Algorithm (as implemented)

- `collapse_step` (clang/collapse/step.c): reduce to WNF, then lift the first
  SUP to the top and return immediately. ERA propagates upward; RED keeps only
  its RHS; INC is left in place for the flattener.
- `collapse_flatten` (clang/collapse/flatten.c): breadth-first traversal with a
  priority queue. SUP increases priority; INC decreases priority. When a branch
  has no SUP, it prints `snf(term)` in quoted mode.

## Label Behavior (pairwise vs cross product)

Different labels commute (cross product):

```
[&A{1,2}, &B{3,4}]
```

```
[1,3]
[1,4]
[2,3]
[2,4]
```

Same labels annihilate pairwise:

```
[&A{1,2}, &A{3,4}]
```

```
[1,2]
[3,4]
```

## Where To Look

- `clang/collapse/step.c`: SUP lifting rules.
- `clang/collapse/flatten.c`: branch enumeration + quoted printing for output.
- `clang/collapse/queue.c`: priority queue used for BFS order.
