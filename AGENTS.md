# AGENTS.md

## Quick Onboarding

HVM4 is a runtime for the Interaction Calculus (IC), a lambda-calculus extension with
explicit duplication (DUP) and superposition (SUP). These primitives enable optimal
sharing for lazy evaluation, even inside lambdas. This repo is the C runtime:
parse source -> build static book terms -> lazily allocate dynamic heap terms ->
reduce with WNF/SNF interactions -> print results.

Key terms:
- static/book term: immutable definition stored in the book (de Bruijn levels).
- dynamic term: mutable heap term used during evaluation (linked by pointers).
- WNF: weak normal form (head reduction with interactions).
- SNF: strong normal form (full reduction).
- CNF: collapsed normal form (full lambda-calculus readback).
- interaction: a rewrite rule (APP-LAM, DUP-SUP, etc.).

## Build and Test

```bash
# Build
cd clang && clang -O2 -o main main.c

# Run a file
./clang/main test/file.hvm4 -s -C10

# Run all tests
./test/_all_.sh
```

## Docs Map

- `README.md`: entry point, build/run examples, links.
- `STYLEGUIDE.md`: authoritative C style rules for `clang/`.
- `docs/theory/interaction_calculus.md`: IC theory + examples.
- `docs/hvm4/core.md`: core term AST and grammar.
- `docs/hvm4/memory.md`: term layout, heap representation, linked/quoted terms.
- `docs/hvm4/collapser.md`: CNF readback and collapse algorithm.
- `docs/hvm4/interactions/*.md`: one file per WNF interaction; mirrors the sequent
  calculus comment in the matching `clang/wnf/<name>.c`.

## Code Map (C Runtime)

### Top-Level Entry
- `clang/hvm4.c`: single translation unit; defines tags/bit layout/globals and
  includes every module in build order. Start here to understand the whole runtime.
- `clang/main.c`: CLI entry point and runtime setup.

### Term Representation
- `clang/term/new.c`: pack a term word from fields.
- `clang/term/tag.c`: extract tag.
- `clang/term/ext.c`: extract ext.
- `clang/term/val.c`: extract val.
- `clang/term/arity.c`: arity per tag.
- `clang/term/clone.c`: duplication helper.
- `clang/term/sub/get.c`: read SUB bit.
- `clang/term/sub/set.c`: set/clear SUB bit.
- `clang/term/new/*.c`: constructors for each tag; `clang/term/new/_.c` allocates
  heap nodes.

### Parser
- `clang/parse/*.c`: lexer utilities, binding stack, and definition parsing.
- `clang/parse/term/*.c`: term parsers; `clang/parse/term/_.c` dispatches.

### Evaluation
- `clang/wnf/_.c`: stack-based WNF evaluator and interaction dispatch.
- `clang/wnf/*.c`: one interaction per file; see matching doc in
  `docs/hvm4/interactions/`.
- `clang/snf/_.c`: SNF entry point and heap anchoring.
- `clang/snf/at.c`: SNF traversal, quoting, and cycle handling.

### Collapse (CNF Readback)
- `clang/collapse/step.c`: lift one SUP to the top, without recursing into branches.
- `clang/collapse/flatten.c`: BFS enumeration of SUP branches; prints quoted SNF.
- `clang/collapse/inject.c`: inject collapsed branches into templates.
- `clang/collapse/queue.c`: priority queue for collapse ordering (INC affects priority).

### Printing and Names
- `clang/print/term.c`: term pretty-printer (dynamic/static modes).
- `clang/print/name.c`: alpha name generation.
- `clang/print/utf8.c`: UTF-8 printing helpers.
- `clang/nick/*.c`: base64-ish name encoding/decoding utilities.
- `clang/table/*.c`: global name table (id <-> string) with lookup helpers.

### Heap and System
- `clang/heap/alloc.c`: heap allocation helpers.
- `clang/heap/subst_var.c`: install lam substitutions.
- `clang/heap/subst_cop.c`: install dup substitutions.
- `clang/sys/error.c`: error formatting.
- `clang/sys/file_read.c`: file read utility.
- `clang/sys/path_join.c`: path joining.
- `clang/prelude/_.c`: prelude stub (empty).

## Naming Rule (Critical)

The file path is the function name: replace `/` with `_`, drop `.c`. Example:
`wnf/app_lam.c` defines `wnf_app_lam()`. `_.c` represents the directory root.
