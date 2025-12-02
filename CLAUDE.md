# CLAUDE.md

## What This Is

HVM4 is a term rewrite system / runtime for the Interaction Calculus.
- The theoretical spec is in `README.md`.
- The C implementation is in `clang/`.
- The C spec is in `clang/README.md`.

## Build and Test

```bash
# Build
cd clang && clang -O2 -o main main.c

# Run a file
./clang/main test/file.hvm4 -s -C

Where:
- `-s` shows performance stats
- `-C` collapses superpositions (use it by default)

# Run all tests
./test/_all_.sh
```

## Code Architecture

### File Organization (CRITICAL)

**The file path IS the function name.** Replace `/` with `_`, drop `.c`:

```
term/tag.c       →  term_tag()
term/new/lam.c   →  term_new_lam()
prim/add.c       →  prim_add()
wnf/app_lam.c    →  wnf_app_lam()
```

`_.c` represents the directory itself:

```
snf/_.c          →  snf()
collapse/_.c     →  collapse()
parse/term/_.c   →  parse_term()
```

This is strictly enforced. Read `clang/STYLE.md` before writing any code.

### Key Modules in `clang/`

- `hvm4.c` — root file that `#include`s everything
- `main.c` — CLI entry point
- `term/` — term representation (tag, val, ext, constructors)
- `parse/` — parser (source → AST)
- `wnf/` — weak normal form evaluator (interaction rules)
- `snf/` — strong normal form evaluator
- `prim/` — primitive operations (add, mul, eq, etc.)
- `collapse/` — superposition extraction

### Term Representation

64-bit term pointer: `SUB(1) | TAG(7) | EXT(24) | VAL(32)`

- SUB: is this heap entry a substitution?
- TAG: term type (APP, LAM, SUP, etc.)
- EXT: label/name (24-bit, base64-encoded)
- VAL: heap address or immediate value

### Evaluation

Stack-based WNF evaluator in `wnf/_.c`.
Interaction rules are in `wnf/` named by pattern:
- `app_lam.c` handles `(λx.f a)`
- `dup_sup.c` handles `! X &L = &R{a,b}`
- etc.

## Test Format

Tests are `.hvm4` files with expected output in trailing `//` comments:

```
@main = ((@add 1) 2)
// 3
```

Always run all tests after each change.
