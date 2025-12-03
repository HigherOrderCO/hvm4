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
| Op2 ::= Term Oper Term
| Eql ::= Term "==" Term
| DSu ::= "&" "(" Term ")" "{" Term "," Term "}"
| DDu ::= "!" Name "&" "(" Term ")" "=" Term ";" Term
| Red ::= Term "~>" Term
| Uns ::= "!" "$" "{" Name "," Name "}" ";" Term
```

Where:
- `Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $`
- `[T]  ::= any sequence of T separated by ","`
- `Oper ::= "+" | "-" | "*" | "/" | "%" | "&&" | "||" | "^" | "~" | "<<" | ">>" | "==" | "!=" | "<" | "<=" | ">" | ">="`

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

Numeric operations are strict on both arguments. The evaluator reduces the
left argument first, then the right argument, then performs the operation.

```
(&{} + y)
---------- op2-era-l
&{}

(&L{a,b} + y)
---------------------- op2-sup-l
! Y &L = y
&L{(a + Y₀), (b + Y₁)}

(#n + &{})
---------- op2-era-r
&{}

(#n + &L{a,b})
---------------------- op2-sup-r
&L{(#n + a), (#n + b)}

(#a + #b)
---------- op2-num
#(a + b)
```

Available operators:
- Arithmetic: `+` `-` `*` `/` `%`
- Bitwise: `&&` `||` `^` `~` `<<` `>>`
- Comparison: `==` `!=` `<` `<=` `>` `>=`

The `~` operator computes bitwise NOT: `(0 ~ x)` returns `~x`.

Equality Interactions
---------------------

Equality `(a == b)` performs structural comparison of arbitrary terms. It is
strict on both arguments (left first, then right). Returns `#1` if equal, `#0`
if not.

```
(&{} == b)
---------- eql-era-l
&{}

(&L{a0,a1} == b)
---------------------- eql-sup-l
! B &L = b
&L{(a0 == B₀), (a1 == B₁)}

(a == &{})
---------- eql-era-r
&{}

(a == &L{b0,b1})
---------------------- eql-sup-r
! A &L = a
&L{(A₀ == b0), (A₁ == b1)}

(#a == #b)
---------- eql-num
#(a == b)

(λax.af == λbx.bf)
------------------ eql-lam
X := fresh_nam()
ax ← X
bx ← X
af == bf

(#K{a0,a1...} == #K{b0,b1...})
------------------------------ eql-ctr
(a0 == b0) & (a1 == b1) & ...

(λ{#K:ah;am} == λ{#K:bh;bm})
---------------------------- eql-mat
(ah == bh) & (am == bm)

(λ{af} == λ{bf})
---------------- eql-use
af == bf

(^n == ^n)
---------- eql-nam
#1

(^(af ax) == ^(bf bx))
---------------------- eql-dry
(af == bf) & (ax == bx)

(_ == _)
-------- eql-other
#0
```

Note: The `&` in results like `(a0 == b0) & (a1 == b1)` represents boolean AND
via numeric operations (can be implemented as `(a * b)` or bitwise `(a && b)`).
The `eql-other` rule catches all mismatched type/tag combinations.

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

Unscoped Binding Interaction
-----------------------------

Unscoped bindings allow the creation of lambdas whose variables can escape their normal scope.
The body is a function `λf.λv.f` that receives the lambda and its variable.

```
! ${f, v}; t
------------------- uns
t(λy.λ$x.y, $x)
```

Reference Interaction
---------------------

```
@foo
---------------------- ref
@{}(book.foo)
```

Reduction Interactions
----------------------

Reductions `f ~> g` represent a term `g` that is guarded by `f`. When applied,
both sides receive the argument, but only `g` continues reducing. The `f` side
tracks the "original" computation for reference semantics.

```
! X &L = f ~> g
--------------- dup-red
! F &L = f
! G &L = g
X₀ ← F₀ ~> G₀
X₁ ← F₁ ~> G₁

((f ~> &{}) a)
-------------- app-red-era
&{}

((f ~> &L{x,y}) a)
------------------ app-red-sup
! F &L = f
! A &L = a
&L{((F₀ ~> x) A₀)
  ,((F₁ ~> y) A₁)}

((f ~> λx.g) a)
--------------- app-red-lam
x ← a
(f a) ~> g

((f ~> (g ~> h)) x)
------------------- app-red-red
((f x) ~> ((g ~> h) x))

((f ~> λ{#K:h; m}) &{})
----------------------- app-red-mat-era
&{}

((f ~> λ{#K:h; m}) &L{a,b})
--------------------------- app-red-mat-sup
! F &L = f
! H &L = h
! M &L = m
&L{((F₀ ~> λ{#K:H₀; M₀}) a)
  ,((F₁ ~> λ{#K:H₁; M₁}) b)}

((f ~> λ{#K:h; m}) #K{a,b})
--------------------------- app-red-mat-ctr-match
((λa.λb.(f #K{a,b}) ~> h) a b)

((f ~> λ{#K:h; m}) #L{a,b})
--------------------------- app-red-mat-ctr-miss
((f ~> m) #L{a,b})

((f ~> λ{n:z;s}) &{})
--------------------- app-red-swi-era
&{}

((f ~> λ{n:z;s}) &L{a,b})
------------------------- app-red-swi-sup
! F &L = f
! Z &L = z
! S &L = s
&L{((F₀ ~> λ{n:Z₀;S₀}) a)
  ,((F₁ ~> λ{n:Z₁;S₁}) b)}

((f ~> λ{n:z;s}) #n)
-------------------- app-red-swi-match
(f #n) ~> z

((f ~> λ{n:z;s}) #m)
-------------------- app-red-swi-miss
((λp.(f p) ~> s) #m)

((f ~> λ{g}) &{})
----------------- app-red-use-era
&{}

((f ~> λ{g}) &L{a,b})
--------------------- app-red-use-sup
! F &L = f
! G &L = g
&L{((F₀ ~> λ{G₀}) a)
  ,((F₁ ~> λ{G₁}) b)}

((f ~> λ{g}) x)
--------------- app-red-use-val
(f x) ~> (g x)

((f ~> #K{...}) a)
------------------ app-red-ctr
^((f ~> #K{...}) a)

((f ~> ^n) a)
------------- app-red-nam
^((f ~> ^n) a)

((f ~> ^(g x)) a)
----------------- app-red-dry
^((f ~> ^(g x)) a)
```
