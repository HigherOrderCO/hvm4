# Style Guide

Abide to the guidelines below strictly!

## File Organization: The Path is the Function Name

Every function MUST live at a predictable path.
- To find `foo_bar_baz()`, open `foo/bar/baz.c`.
- To know what's in `foo/bar/baz.c`, look for `foo_bar_baz()`.
No exceptions.

The rule is: replace `/` with `_`, drop `.c`.

```
term/tag.c       →  term_tag()
term/new/lam.c   →  term_new_lam()
prim/add.c       →  prim_add()
wnf/app_lam.c    →  wnf_app_lam()
```

The `_.c` file represents the directory itself (the "main" function for that path):

```
snf/_.c          →  snf()
collapse/_.c     →  collapse()
parse/term/_.c   →  parse_term()
```

Use a directory when a function has sub-functions; use a file when it doesn't:

```
term/tag.c                  # no children → file
term/new/_.c + lam.c + ...  # has children → directory
```

A file may include helper variants, but the primary function must match the filename:

```c
// term/new/lam.c
fn Term term_new_lam_at(...) { ... }  // helper variant
fn Term term_new_lam(...) { ... }     // primary (matches filename)
```

The filesystem is the index. Do NOT break this pattern.

## NEVER write single-line ifs, loops, statements, functions.

Don't:
```c
if { ... }
while { ... }
u32 foo(x) { ... }
foo(); bar();
```

Do:
```c
if {
  ...
}
while {
  ...
}
u32 foo(x) {
  ...
}
foo();
bar();
```

## ALWAYS use switch for Term pattern matching.

Don't:
```c
if (tag == FOO) {
  ...
} else if (tag == BAR) {
  ...
} ...
```

Do:
```c
switch (tag) {
  case FOO: {
    ...
  }
  case BAR: {
    ...
  }
}
```

## Aggressively abstract common patterns (DRY).

When a pattern is repeated in multiple places:

Don't:
```c
fn Term <many_fns>(...) {
  ...
  if (side == 0) {
    subst_var(loc, res1);
    return res0;
  } else {
    subst_var(loc, res0);
    return res1;
  }
}
```

Do:
```c
fn Term subst_cop(u8 side, u32 loc, Term r0, Term r1) {
  subst_var(loc, side == 0 ? r1 : r0);
  return side == 0 ? r0 : r1;
}
fn Term <many_fns>(...) {
  ...
  return subst_cop(side, loc, res0, res1);
}
```

In general, spend some time reasoning about opportunities to apply the DRY
principle, extracting common patterns out to reduce code size. We greatly
appreciate simplicity brought by good abstractions!

## Align columns whenever reasonable; adjust names as needed.

Don't:
```c
Term abc = foo;
u32 x = 123;
Term the_amazing_cat = bar;
```

Do:
```c
Term abc = foo;
u32  x   = 123;
Term cat = bar;
```

Don't:
```c
foo[x] = 123;
foo[x+1] = 456;
```

Do:
```c
foo[x+0] = 123;
foo[x+1] = 456;
```
