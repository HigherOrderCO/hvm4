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
| Lam ::= "λ" Name "." Term
| App ::= "(" Term " " Term ")"
| Alo ::= "@" "{" [Name] "}" Term
| DSp ::= "&" "(" Term ")" "{" Term "," Term "}"
| DDp ::= "!" Name "&" "(" Term ")" "=" Term ";" Term
| Num ::= Number
| Sp0 ::= "/Sp0" "(" Term ")"
| Sp1 ::= "/Sp1" "(" Term ")"
| Inc ::= "+" Term
```

Where:
- `Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $`
- `[T]  ::= any sequence of T separated by ","`

In HVM4:
- Variables are affine; they must occur at most once.
- Variables range globally; they can occur anywhere.

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

Reference Interaction
---------------------

```
@foo
---------------------- ref
foo ~> @{}(book.foo)
```

Numerical Interactions
----------------------

```
+N
------ suc-num
N+1

+&L{x,y}
--------- suc-sup
&L{+x,+y}

+&{}
--------- suc-era
&{}

/Sp0(N)
--------- sp0-num
((N * 16293) + 1) % 0xFFFF

/Sp0(&L{x,y})
------------------ sp0-sup
&L{/Sp0(x),/Sp0(y)}

/Sp0(&{})
---------- sp0-era
&{}

/Sp1(N)
--------- sp1-num
((N * 32677) + 3) % 0xFFFF

/Sp1(&L{x,y})
------------------ sp1-sup
&L{/Sp1(x),/Sp1(y)}

/Sp1(&{})
---------- sp1-era
&{}
```

Dynamic Label Interactions
---------------------------

```
&(L){a,b}
--------- dsp-num
&L{a,b}

&(&L{a,b}){c,d}
---------------------------- dsp-sup
&L{&(a){C₀,D₀}, &(b){C₁,D₁}}

&(&{}){a,b}
----------- dsp-era
&L{a,b}

! &(L) = v; t
-------------- ddp-num
!X &L = v; (t X₀ X₁)

! &(&L{a,b}) = v; t
--------------------- ddp-sup
!V &L = v;
!T &L = t;
&L{!Y&(a)=V₀; T₀, !Z&(b)=V₁; T₁}

! &(&{}) = v; t
-------------- ddp-era
(t &{} &{})
```
