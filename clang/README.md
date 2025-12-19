# HVM4 Runtime Implementation in C

This file implements the HVM4, an Interaction Calculus runtime, ported from
Haskell. It includes parsing, stringification, and a stack-based weak normal
form (WNF) evaluator with all interaction rules.

## Term Pointer Layout (64-bit)

| SUB  (1 bit)   ::= marks heap slot as containing a substitution
| TAG  (7 bits)  ::= constructor variant (APP, LAM, SUP, etc.)
| EXT  (24 bits) ::= dup label, ctr name, or ref name
| VAL  (32 bits) ::= heap address or unboxed value

## Tag Encoding

- DP0/DP1: Runtime dup copies (sides 0 and 1 of a DUP node)
- DUP: Dup term (syntactic binder `!x&L = val; body`)
- C00...C16: Constructor tags encode arity directly (C00+n for n fields)
- Names (variable, constructor, reference) use 6-char base64 strings encoded
  as 24-bit integers fitting in the EXT field

## Memory Model (No Separate Maps)

Unlike the Haskell version which uses IntMaps for 'dups' and 'subs', this
implementation stores everything directly on the heap:

- DUP terms (syntactic): stored inline as a 2-slot pair `[expr, body]` with
  label in `ext`.
- DUP nodes (runtime): represented by DP0/DP1 terms that share an expr
  location (one heap slot). There is no dup body; the DUP node is the expr
  slot that holds the live duplication state (label stored in DP0/DP1's `ext` field).

DUP terms evaluate to their body in WNF; duplication happens only when DP0/DP1 are forced.

- Substitutions: Stored where the lambda body, or DUP node expr slot,
  was. When app_lam fires, the argument replaces the lambda body slot. The
  SUB bit distinguishes actual terms from substitutions, allowing VAR, DP0
  and DP1 to detect whether their target is a binding node or a subst.

## Book vs Runtime Term Representation

Book terms (parsed definitions) use de Bruijn levels and are immutable:
  - BJV: ext = 0         ; val = bru_level
  - BJ_: ext = dup_label ; val = bru_level
  - LAM: ext = bru_level ; val = body_location
  - DUP: ext = dup_label ; val = dup_term_location (expr, body)
  - NAM: ext = name_id   ; val = 0  (literal ^name)
Levels are 1-based from the definition root; level 0 denotes an unscoped var.

Runtime terms (after ALO allocation) use heap locations:
  - VAR : ext = 0         ; val = binding_lam_body_location
  - DP_ : ext = dup_label ; val = binding_dup_expr_location
  - LAM : ext = 0         ; val = body_location
  - DUP : ext = dup_label ; val = dup_term_location (expr, body)
Quoted runtime terms (from `snf_at(..., quoted = 1)`) use the same representation
as book terms (LAM.ext = level, BJV/BJ0/BJ1 levels).

## ALO (Allocation) Nodes

ALO terms reference immutable book entries and lazily convert them to
runtime terms. Each ALO stores a pair (bind_list, book_term_loc) packed
into a single 64-bit heap word:
  - Low 32 bits: book term location
  - High 32 bits: bind list head (linked list of binder locations)

The bind list maps de Bruijn levels to runtime heap locations of binding
LAM/DUP terms. When an ALO interaction occurs, one layer of the book term
is extracted and converted to a runtime term.
ALO terms store the bind list length in `ext` to index levels directly.

## Pretty Printer (print/)

The printer has two modes that correspond to the two term representations:

- **Runtime mode** (default): terms are linked by heap locations. The printer
  assigns a globally unique name to each lambda body location, and prints every
  VAR that points to that location using the same name. This avoids lexical
  renaming issues, so unscoped variables still print with their binders.
- **Quoted mode** (used for ALO): terms are immutable book terms with de Bruijn
  levels (BJV/BJ0/BJ1). Lambdas are printed using depth-based names, and
  BJV/BJ0/BJ1 try to use the ALO substitution list to show concrete runtime
  values when available.

Key rules the printer must obey:

- **Substitution chasing**: VAR/DP0/DP1 can point to heap slots with the SUB bit
  set. In that case the printer must unmark and print the substituted term
  instead of the variable itself. This applies both to the main term and to the
  ALO substitution list (when BJV/BJ0/BJ1 resolve to runtime bindings).
- **Floating DUPs**: a DUP node is the shared expr location referenced by
  DP0/DP1. The printer records a dup node when it first sees DP0/DP1 and prints
  all discovered dups after the main term as `!A&L=val;`. Printing a dup can
  discover more dups, so this continues until the list is exhausted.
- **Names**: lambda names are lower-case (a, b, ..., aa, ab, ...), dup names are
  upper-case (A, B, ..., AA, AB, ...). These names are global, keyed by heap
  location, not by lexical scope. The printer uses fixed-size name tables
  limited to 65536 entries for lambdas and dups.

The printer entry points are:

- `print_term`: runtime mode (global naming + floating dups).
- `print_term_quoted`: prints quoted terms (BJV/BJ0/BJ1) with depth-based names.

## SNF Quoted Mode

`snf_at(loc, depth, quoted)` normalizes the heap term at `loc` to strong normal
form. `snf(term, depth, quoted)` anchors `term` in the heap and calls `snf_at`.
In quoted mode, LAM and DUP binders install **BJ* placeholders** by reusing the
runtime substitution mechanism:

- **LAM**: its body slot is marked with `BJV` carrying the binder level
  (`depth + 1`), then the body is normalized in-place. The returned LAM has
  `ext = depth + 1`, making quoted lambdas unambiguous (runtime lambdas always
  have `ext = 0`).
- **DUP** (dup term): its expr slot is replaced with `&L{BJ0,BJ1}` at level `depth + 1`,
  then the expr and body are normalized to build a quoted DUP term.
- **DP0/DP1** (runtime mode): normalize the DUP node expr at its heap
  location so floating dups are reduced; a visited loc set avoids cycles.

Any VAR/DP0/DP1 that escape scoping in quoted mode become BJ* at the current
depth. This keeps book and quoted runtime terms structurally identical while
relying on runtime substitutions instead of binder tracking.
Collapse uses `quoted = 1` to preserve book-style output, while non-collapsed
runs use `quoted = 0` and print with global names.

## Stack-Based WNF Evaluator

To avoid stack overflow, WNF uses an explicit stack with two phases:

REDUCE phase: Push eliminators onto stack and descend into their targets
  - APP: push frame, enter function
  - MAT: push frame, enter scrutinee (after MAT reaches head position)
  - DP0/DP1: push frame, enter DUP node expr

APPLY phase: Pop frames and dispatch interactions based on WHNF result

DUP terms and ALO don't push stack frames since they immediately trigger their
respective interactions without requiring sub-WNF results first.

## Internal-Only Constructs

These nodes are internal and not parseable:
- ALO: lazy alloc
- NAM: stuck variable (^name)
- DRY: stuck application (^(f x))
- BJV/BJ0/BJ1: quoted bound variables (de Bruijn levels)

## Collapse Function

Extracts superpositions (SUP) to the top level. For each term type:
1. Collapse subterms recursively
2. Build a template: nested lambdas that reconstruct the term
3. Call inject(template, collapsed_subterms)
This will move the term to inside SUP layers, 'collapsing' it.

Key: VARs in templates must point to their binding lambda's body location.
For LAM, the inner lambda MUST reuse lam_loc so existing VARs stay bound.
