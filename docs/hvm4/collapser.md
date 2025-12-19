# Collapser

WIP/TODO: this document is a draft and will be expanded with full algorithmic
notes and invariants.

## Collapse Function

Collapse extracts superpositions (SUP) to the top level. For each term type:
1. Collapse subterms recursively
2. Build a template: nested lambdas that reconstruct the term
3. Call `inject(template, collapsed_subterms)`

Key rule: VARs in templates must point to their binding lambda's body location.
For LAM, the inner lambda must reuse `lam_loc` so existing VARs stay bound.
