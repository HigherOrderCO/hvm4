HVM4
====
HVM4 is a term rewrite system for the following grammar:

```
Term ::=
| Var ::= Name
| Dp0 ::= Name "₀"
| Dp1 ::= Name "₁"
| Ref ::= "@" Name
| Nam ::= "^" Name
| Dry ::= "^" "(" Term " " Term ")"
| Era ::= "&{}"
| Sup ::= "&" Name "{" Term "," Term "}"
| Dup ::= "!" Name "&" Name "=" Term ";" Term
| Ctr ::= "#" Name "{" [Term] "}"
| Mat ::= "λ" "{" "#" Name ":" Term ";" Term "}"
| Swi ::= "λ" "{" Num ":" Term ";" Term "}"
| Use ::= "λ" "{" Term "}"
| Lam ::= "λ" Name "." Term
| App ::= "(" Term " " Term ")"
| Alo ::= "@" "{" [Name] "}" Term
| Num ::= Integer
| Op2 ::= "@@" Oper "(" Term "," Term ")"
| DSu ::= "&" "(" Term ")" "{" Term "," Term "}"
| DDu ::= "!" Name "&" "(" Term ")" "=" Term ";" Term
```

Where:
- `Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $`
- `[T]  ::= any sequence of T separated by ","`
- `Oper ::= add | sub | mul | div | mod | and | or | xor | lsh | rsh | not | eq | ne | lt | le | gt | ge`

In HVM4:
- Variables are affine; they must occur at most once.
- Variables range globally; they can occur anywhere.
- Numbers are written as `#n` in interaction rules (e.g., `#42`). This is distinct
  from constructors which use `#Name{...}` syntax (e.g., `#Pair{a,b}`).

Stuck Terms (DRY)
-----------------

When a term cannot reduce further because it's applied to something that isn't
a function, it becomes "stuck". These stuck applications are represented as DRY
(dry) terms using `^(f x)` syntax. For example:
- `(#K{a,b} x)` → `^(#K{a,b} x)` (constructor applied to argument)
- `(^n x)` → `^(^n x)` (name applied to argument)
- `(^(f x) y)` → `^(^(f x) y)` (stuck term applied to argument)

Stuck terms propagate through the system and can be duplicated and manipulated,
but they don't reduce until the head becomes a lambda or eliminator.

Application Interactions
------------------------

```
(&{} a)
------- app-era
&{}

(&L{f,g} a)
----------------- app-sup
! A &L = a
&L{(f A₀),(g A₁)}

(λx.f a)
-------- app-lam
x ← a
f

(#K{...} a)
----------- app-ctr
^(#K{...} a)

(λ{#K:h; m} &{})
---------------- app-mat-era
&{}

(λ{#K:h; m} &L{a,b})
-------------------- app-mat-sup
! H &L = h
! M &L = m
&L{(λ{#K:H₀; M₀} a)
  ,(λ{#K:H₁; M₁} b)}

(λ{#K:h; m} #K{a,b})
-------------------- app-mat-ctr-match
(h a b)

(λ{#K:h; m} #L{a,b})
-------------------- app-mat-ctr-miss
(m #L{a,b})

(λ{n:f;g} &{})
-------------- app-swi-era
&{}

(λ{n:f;g} &L{a,b})
--------------------- app-swi-sup
! F &L = f
! G &L = g
&L{(λ{n:F₀;G₀} a), (λ{n:F₁;G₁} b)}

(λ{n:f;g} #m)
-------------- app-swi-num
if n == m: f
else: (g #m)

(λ{f} &{})
---------- use-era
&{}

(λ{f} &L{a,b})
----------------- use-sup
! F &L = f
&L{(λ{F₀} a), (λ{F₁} b)}

(λ{f} x)
--------- use-val
(f x)

(^n a)
------- app-nam
^(^n a)

(^(f x) a)
----------- app-dry
^(^(f x) a)
```

Duplication Interactions
------------------------

```
! X &L = &{}
------------ dup-era
X₀ ← &{}
X₁ ← &{}

! X &L = &R{a,b}
---------------- dup-sup
if L == R:
  X₀ ← a
  X₁ ← b
else:
  ! A &L = a
  ! B &L = b
  X₀ ← &R{A₀,B₀}
  X₁ ← &R{A₁,B₁}

! F &L = λx.f
---------------- dup-lam
F₀ ← λ$x0.G₀
F₁ ← λ$x1.G₁
x  ← &L{$x0,$x1}
! G &L = f

! X &L = #K{a,b}
---------------- dup-ctr
! A &L = a
! B &L = b
X₀ ← #K{A₀,B₀}
X₁ ← #K{A₁,B₁}

! X &L = λ{#K:h; m}
------------------- dup-mat
! H &L = h
! M &L = m
X₀ ← λ{#K:H₀; M₀}
X₁ ← λ{#K:H₁; M₁}

! X &L = ^n
----------- dup-nam
X₀ ← ^n
X₁ ← ^n

! X &L = ^(f x)
--------------- dup-dry
! F &L = f
! A &L = x
X₀ ← ^(F₀ A₀)
X₁ ← ^(F₁ A₁)

! X &L = #n
----------- dup-num (via dup-node)
X₀ ← #n
X₁ ← #n

! X &L = λ{n:f;g}
------------------ dup-swi (via dup-node)
! F &L = f
! G &L = g
X₀ ← λ{n:F₀;G₀}
X₁ ← λ{n:F₁;G₁}

! X &L = λ{f}
------------- dup-use (via dup-node)
! F &L = f
X₀ ← λ{F₀}
X₁ ← λ{F₁}
```

Allocation Interactions
-----------------------

```
@{s} n
------ alo-var
s[n]

@{s} n₀
------- alo-dp0
s[n]₀

@{s} n₁
------- alo-dp1
s[n]₁

@{s} @ref
--------- alo-ref
@ref

@{s} ^n
------- alo-nam
^n

@{s} ^(f x)
-------------- alo-dry
^(@{s}f @{s}x)

@{s} &{}
-------- alo-era
&{}

@{s} &L{a,b}
---------------- alo-sup
&L{@{s}a, @{s}b}

@{s} ! x &L = v; t
------------------ alo-dup
x' ← fresh
! x' &L = @{s} v
@{x',s} t

@{s} λx.f
------------ alo-lam
x' ← fresh
λx'.@{x',s}f

@{s} (f x)
------------- alo-app
(@{s}f @{s}x)

@{s} #K{x,y...}
------------------- alo-ctr
#K{@{s}x, @{s}y...}

@{s} λ{#K:h; m}
------------------- alo-mat
λ{#K: @{s}h; @{s}m}
```

Numeric Operation Interactions
------------------------------

Numeric operations use a two-phase reduction. `@@opr(x, y)` is strict on `x`,
and when `x` reduces to a number, it creates `@@opr'(x, y)` which is strict on `y`.
When both arguments are numbers, the operation is performed.

```
@@opr(&{}, y)
------------- op2-era
&{}

@@opr(&L{a,b}, y)
------------------------- op2-sup
! Y &L = y
&L{@@opr(a,Y₀), @@opr(b,Y₁)}

@@opr(#n, y)
------------ op2-num
@@opr'(#n, y)

@@opr'(x, &{})
-------------- op1-era
&{}

@@opr'(x, &L{a,b})
------------------------- op1-sup
! X &L = x
&L{@@opr'(X₀,a), @@opr'(X₁,b)}

@@opr'(#a, #b)
-------------- op1-num
#(a opr b)
```

Where `opr` is one of: add, sub, mul, div, mod, and, or, xor, lsh, rsh, eq, ne, lt, le, gt, ge.
The `not` operation uses `@@not(0, x)` with result `~x`.

Dynamic Superposition Interactions
----------------------------------

Dynamic superpositions allow the label to be computed at runtime.

```
&(&{}){a, b}
------------ dsu-era
&{}

&(&L{x,y}){a, b}
-------------------------- dsu-sup
! A &L = a
! B &L = b
&L{&(x){A₀,B₀}, &(y){A₁,B₁}}

&(#n){a, b}
----------- dsu-num
&n{a, b}
```

Dynamic Duplication Interactions
--------------------------------

Dynamic duplications allow the label to be computed at runtime.
The body is a function `λx₀.λx₁.f` that receives both copies.

```
! X &(&{}) = v; b
----------------- ddu-era
&{}

! X &(&L{x,y}) = v; b
------------------------------ ddu-sup
! V &L = v
! B &L = b
&L{! X &(x) = V₀; B₀, ! X &(y) = V₁; B₁}

! X &(#n) = v; b
---------------- ddu-num
! X &n = v; (b X₀ X₁)
```

Reference Interaction
---------------------

```
@foo
---------------------- ref
foo ~> @{}(book.foo)
```
