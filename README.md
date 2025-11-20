Calculus of Interactions
========================
CoI is a term rewrite system for the following grammar:

```
Term ::=
| Var ::= Name
| Dp0 ::= Name "₀"
| Dp1 ::= Name "₁"
| Ref ::= "@" Name
| Nam ::= "." Name
| Dry ::= "." "(" Term " " Term ")"
| Era ::= "&{}"
| Sup ::= "&" Name "{" Term "," Term "}"
| Dup ::= "!" Name "&" Name "=" Term ";" Term
| Set ::= "*"
| All ::= "∀" Term "." Term
| Lam ::= "λ" Name "." Term
| App ::= "(" Term " " Term ")"
| Sig ::= "Σ" Term "." Term
| Tup ::= Term "," Term
| Get ::= "λ" "{" "," ":" Term ";"? "}"
| Emp ::= "⊥"
| Efq ::= "λ" "{" "}"
| Uni ::= "⊤"
| One ::= "()"
| Use ::= "λ" "{" "()" ":" Term ";"? "}"
| Bol ::= "𝔹"
| Fal ::= "#F"
| Tru ::= "#T"
| If  ::= "λ" "{" "#F" ":" Term ";"? "#T" ":" Term ";"? "}"
| Nat ::= "ℕ"
| Zer ::= "0"
| Suc ::= "1+"
| Swi ::= "λ" "{" "0" ":" Term ";"? "1" "+" ":" Term ";"? "}"
| Lst ::= Term "[]"
| Nil ::= "[]"
| Con ::= Term "<>" Term
| Mat ::= "λ" "{" "[]" ":" Term ";"? "<>" Term ";"? "}"
| And ::= Term "&&" Term
| Eql ::= Term "==" Term
| Gua ::= Term "~>" Term
| Gen ::= "?" Name ":" Term "=" Term "~" Term "&" Term
```

Where:
- `Name ::= any sequence of base-64 chars in _ A-Z a-z 0-9 $`
- `[T]  ::= any sequence of T separated by ","`

In CoI:
- Variables are affine; they must occur at most once.
- Variables range globally; they can occur anywhere.

Reference Interaction
---------------------

```
@foo
-------------------- ref
foo ~> alloc(book.foo)
```

Duplication Interactions
------------------------

```
! X &L = &{}
---------- dup-era
X₀ ← &{}
X₁ ← &{}

! X &L = &R{a,b}
-------------- dup-sup
if L == R:
  X₀ ← a
  X₁ ← b
else:
  ! A &L = a
  ! B &L = b
  X₀ ← &R{A₀,B₀}
  X₁ ← &R{A₁,B₁}

! X &L = *
-------- dup-set
X₀ ← *
X₁ ← *

! X &L = ∀a.b
----------- dup-all
! A &L = a
! B &L = b
X₀ ← ∀A₀.B₀
X₁ ← ∀A₁.B₁

! F &L = λx.f
-------------- dup-lam
F₀ ← λ$x0.G₀
F₁ ← λ$x1.G₁
x  ← &L{$x0,$x1}
! G &L = f

! X &L = Σa.b
----------- dup-sig (NEW)
! A &L = a
! B &L = b
X₀ ← ΣA₀.B₀
X₁ ← ΣA₁.B₁

! X &L = (a,b)
------------ dup-tup (NEW)
! A &L = a
! B &L = b
X₀ ← (A₀,B₀)
X₁ ← (A₁,B₁)

! X &L = λ{,:c}
------------- dup-get (NEW)
! C &L = c
X₀ ← λ{,:C₀}
X₁ ← λ{,:C₁}

! X &L = ⊥
-------- dup-emp (NEW)
X₀ ← ⊥
X₁ ← ⊥

! X &L = λ{}
---------- dup-efq (NEW)
X₀ ← λ{}
X₁ ← λ{}

! X &L = ⊤
-------- dup-uni (NEW)
X₀ ← ⊤
X₁ ← ⊤

! X &L = ()
--------- dup-one (NEW)
X₀ ← ()
X₁ ← ()

! X &L = λ{():u}
-------------- dup-use (NEW)
! U &L = u
X₀ ← λ{():U₀}
X₁ ← λ{():U₁}

! X &L = 𝔹
-------- dup-bol (NEW)
X₀ ← 𝔹
X₁ ← 𝔹

! X &L = #F
--------- dup-fal (NEW)
X₀ ← #F
X₁ ← #F

! X &L = #T
--------- dup-tru (NEW)
X₀ ← #T
X₁ ← #T

! X &L = λ{#F:f;#T:t}
------------------- dup-if (NEW)
! F &L = f
! T &L = t
X₀ ← λ{#F:F₀;#T:T₀}
X₁ ← λ{#F:F₁;#T:T₁}

! X &L = ℕ
-------- dup-nat
X₀ ← ℕ
X₁ ← ℕ

! X &L = 0
-------- dup-zer
X₀ ← 0
X₁ ← 0

! X &L = 1+n
---------- dup-suc
! N &L = n
X₀ ← 1+N₀
X₁ ← 1+N₁

! X &L = λ{0:z;1+:s}
------------------ dup-swi
! Z &L = z
! S &L = s
X₀ ← λ{0:Z₀;1+:S₀}
X₁ ← λ{0:Z₁;1+:S₁}

! X &L = t[]
---------- dup-lst (NEW)
! T &L = t
X₀ ← T₀[]
X₁ ← T₁[]

! X &L = []
----------- dup-nil (NEW)
X₀ ← []
X₁ ← []

! X &L = h<>t
------------- dup-con (NEW)
! H &L = h
! T &L = t
X₀ ← H₀<>T₀
X₁ ← H₁<>T₁

! X &L = λ{[]:n;<>:c}
--------------------- dup-mat (NEW)
! N &L = n
! C &L = c
X₀ ← λ{[]:N₀;<>:C₀}
X₁ ← λ{[]:N₁;<>:C₁}

! X &L = .n
----------- dup-nam
X₀ ← .n
X₁ ← .n

! X &L = .(f x)
--------------- dup-dry
! F &L = f
! A &L = x
X₀ ← .(F₀ A₀)
X₁ ← .(F₁ A₁)

! X &L = f ~> g
--------------- dup-gua
! F &L = f
! G &L = g
X₀ ← F₀ ~> G₀
X₁ ← F₁ ~> G₁
```

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

(λ{,:c} &{})
------------ app-get-era (NEW)
&{}

(λ{,:c} &L{a,b})
---------------- app-get-sup (NEW)
! C &L = c
&L{(λ{,:C₀} a)
  ,(λ{,:C₁} b)}

(λ{,:c} (a,b))
-------------- app-get-tup (NEW)
(c a b)

(λ{} &{})
--------- app-efq-era (NEW)
&{}

(λ{} &L{a,b})
------------- app-efq-sup (NEW)
&L{(λ{} a)
  ,(λ{} b)}

(λ{} ⊥)
------- app-efq-emp (NEW)
λ{} ⊥

(λ{():u} &{})
------------- app-use-era (NEW)
&{}

(λ{():u} &L{a,b})
----------------- app-use-sup (NEW)
! U &L = u
&L{(λ{():U₀} a)
  ,(λ{():U₁} b)}

(λ{():u} ())
------------ app-use-one (NEW)
u

(λ{#F:f;#T:t} &{})
------------------ app-if-era (NEW)
&{}

(λ{#F:f;#T:t} &L{a,b})
---------------------- app-if-sup (NEW)
! F &L = f
! T &L = t
&L{(λ{#F:F₀;#T:T₀} a)
  ,(λ{#F:F₁;#T:T₁} b)}

(λ{#F:f;#T:t} #F)
----------------- app-if-fal (NEW)
f

(λ{#F:f;#T:t} #T)
----------------- app-if-tru (NEW)
t

(λ{0:z;1+:s} &{})
----------------- app-swi-era
&{}

(λ{0:z;1+:s} &L{a,b})
--------------------- app-swi-sup
! Z &L = z
! S &L = s
&L{(λ{0:Z₀;1+:S₀} a)
  ,(λ{0:Z₁;1+:S₁} b)}

(λ{0:z;1+:s} 0)
--------------- app-swi-zer
z

(λ{0:z;1+:s} 1+n)
----------------- app-swi-suc
(s n)

(λ{[]:n;<>:c} &{})
------------------ app-mat-era (NEW)
&{}

(λ{[]:n;<>:c} &L{a,b})
---------------------- app-mat-sup (NEW)
! N &L = n
! C &L = c
&L{(λ{[]:N₀;<>:C₀} a)
  ,(λ{[]:N₁;<>:C₁} b)}

(λ{[]:n;<>:c} [])
----------------- app-mat-nil (NEW)
n

(λ{[]:n;<>:c} h<>t)
------------------- app-mat-con (NEW)
(c h t)

(.n a)
------- app-nam
.(.n a)

(.(f x) a)
----------- app-dry
.(.(f x) a)
```

Conjunction Interactions
------------------------

```
&{} && b
-------- and-era
&{}

&L{a0,a1} && b
-------------- and-sup
! B &L = b
&L{B₀ && a0
  ,B₁ && a1}

#F && b
------- and-fal (NEW - now uses #F instead of 0)
#F

#T && b
------- and-tru (NEW - now uses #T instead of 1)
b
```

Equality Interactions
---------------------

```
&{} == b
-------- eql-era-any
&{}

&L{a0,a1} == b
-------------- eql-sup-any
! &L B = b
&L{a0 == B₀
  ,a1 == B₁}

a == &{}
-------- eql-any-era
&{}

a == &L{b0,b1}
-------------- eql-any-sup
! &L A = a
&L{A₀ == b0
  ,A₁ == b1}

* == *
------ eql-set-set
1

∀aA.aB == ∀bA.bB
------------------ eql-all-all
(aA==bA)&&(aB==bB)

λax.af == λbx.bf
---------------- eql-lam-lam
ax ← X
bx ← X
af == bf

ΣaA.aB == ΣbA.bB
------------------ eql-sig-sig
(aA==bA)&&(aB==bB)

(a1,a2) == (b1,b2)
------------------ eql-tup-tup
(a1==b1)&&(a2==b2)

λ{,:ac} == λ{,:bc}
------------------ eql-get-get
ac == bc

⊥ == ⊥
------ eql-emp-emp
1

λ{} == λ{}
---------- eql-efq-efq
1

⊤ == ⊤
------ eql-uni-uni
1

() == ()
-------- eql-one-one
1

λ{():au} == λ{():bu}
-------------------- eql-use-use
au == bu

𝔹 == 𝔹
------ eql-bol-bol
1

#F == #F
-------- eql-fal-fal
1

#T == #T
-------- eql-tru-tru
1

#F == #T
-------- eql-fal-tru
0

#T == #F
-------- eql-tru-fal
0

λ{#F:af;#T:at} == λ{#F:bf;#T:bt}
-------------------------------- eql-if-if
(af==bf)&&(at==bt)

ℕ == ℕ
------ eql-nat-nat
1

0 == 0
------ eql-zer-zer
1

1+a == 1+b
---------- eql-suc-suc
a == b

λ{0:az;1+:as} == λ{0:bz;1+:bs}
------------------------------ eql-swi-swi
(az==bz)&&(as==bs)

aT[] == bT[]
---------- eql-lst-lst
aT == bT

[] == []
------ eql-nil-nil
1

ah<>at == bh<>bt
-------------- eql-con-con
(ah==bh)&&(at==bt)

λ{[]:an;<>:ac} == λ{[]:bn;<>:bc}
------------------------------- eql-mat-mat
(an==bn)&&(ac==bc)

.x == .y
-------- eql-nam-nam
if x == y:
  1
else:
  0

.(af ax) == .(bf bx)
---------------------- eql-dry-dry
(af == bf) && (ax == bx)

(af~>ag) == b
----------- eql-gua
TODO
```

Guarded Application Interactions
--------------------------------

```
((f ~> &{}) a)
-------------- app-gua-era
&{}

((f ~> &L{x,y}) a)
------------------ app-gua-sup
! &L F = f
! F &L = f
! A &L = a
&L{((F₀ ~> x) A₀)
  ,((F₁ ~> y) A₁)}

((f ~> λx.g) a)
--------------- app-gua-lam
x ← a
(f x) ~> g

((f ~> (g ~> h)) x)
----------------------- app-gua-gua
((f x) ~> ((g ~> h) x))

((f ~> λ{,:c}) &{})
------------------- app-gua-get-era (NEW)
&{}

((f ~> λ{,:c}) &L{a,b})
----------------------- app-gua-get-sup (NEW)
! F &L = f
! C &L = c
&L{((F₀ ~> λ{,:C₀}) a)
  ,((F₁ ~> λ{,:C₁}) b)}

((f ~> λ{,:c}) (a,b))
---------------------------- app-gua-get-tup (NEW)
((λx.λy.(f (x,y)) ~> c) a b)

((f ~> λ{}) &{})
---------------- app-gua-efq-era (NEW)
&{}

((f ~> λ{}) &L{a,b})
-------------------- app-gua-efq-sup (NEW)
! F &L = f
&L{((F₀ ~> λ{}) a)
  ,((F₁ ~> λ{}) b)}

((f ~> λ{():u}) &{})
-------------------- app-gua-use-era (NEW)
&{}

((f ~> λ{():u}) &L{a,b})
------------------------ app-gua-use-sup (NEW)
! F &L = f
! U &L = u
&L{((F₀ ~> λ{():U₀}) a)
  ,((F₁ ~> λ{():U₁}) b)}

((f ~> λ{():u}) ())
------------------- app-gua-use-one (NEW)
(f ()) ~> u

((g ~> λ{#F:f;#T:t}) &{})
------------------------- app-gua-if-era (NEW)
&{}

((g ~> λ{#F:f;#T:t}) &L{a,b})
----------------------------- app-gua-if-sup (NEW)
! G &L = g
! F &L = f
! T &L = t
&L{((G₀ ~> λ{#F:F₀;#T:T₀}) a)
  ,((G₁ ~> λ{#F:F₁;#T:T₁}) b)}

((g ~> λ{#F:f;#T:t}) #F)
------------------------ app-gua-if-fal (NEW)
(g #F) ~> f

((g ~> λ{#F:f;#T:t}) #T)
------------------------ app-gua-if-tru (NEW)
(g #T) ~> t

((f ~> λ{[]:n;<>:c}) &{})
------------------------- app-gua-mat-era (NEW)
&{}

((f ~> λ{[]:n;<>:c}) &L{a,b})
----------------------------- app-gua-mat-sup (NEW)
! F &L = f
! N &L = n
! C &L = c
&L{((F₀ ~> λ{[]:N₀;<>:C₀}) a)
  ,((F₁ ~> λ{[]:N₁;<>:C₁}) b)}

((f ~> λ{[]:n;<>:c}) [])
------------------------ app-gua-mat-nil (NEW)
(f []) ~> n

((f ~> λ{[]:n;<>:c}) h<>t)
--------------------------- app-gua-mat-con (NEW)
((λh.λt.(f h<>t) ~> c) h t)

((f ~> λ{0:z;1+:s}) &{})
------------------------ app-gua-swi-era
&{}

((f ~> λ{0:z;1+:s}) &L{a,b})
---------------------------- app-gua-swi-sup
! F &L = f
! Z &L = z
! S &L = s
&L{((F₀ ~> λ{0:Z₀;1+:S₀}) a)
  ,((F₁ ~> λ{0:Z₁;1+:S₁}) b)}

((f ~> λ{0:z;1+:s}) 0)
---------------------- app-gua-swi-zer
(f 0) ~> z

((f ~> λ{0:z;1+:s}) 1+n)
------------------------ app-gua-swi-suc
((λp.(f 1+p) ~> s) n)
```

SupGen Interactions
-------------------

... TODO ...

```
?L : ∀𝔹.b = f ~ fs & xs
--------------------- gen-all-bol
! B  &L = b
! F  &L = f
! FS &L = FS
! XS &L = XS
&L{
  λx.
    ?S₀(L) : B₀ = (F₀ x) ~ (map λk.(k x) FS₀) & x<>XS₀
  λ{
    #F: ?S₀(L) : B₁ = (F₁ #F) ~ (map λk.(k #F) FS₁) & x<>XS₁
    #T: ?S₁(L) : B₁ = (F₁ #T) ~ (map λk.(k #T) FS₁) & x<>XS₁
  }
}
```
