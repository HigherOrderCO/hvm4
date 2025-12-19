# DUP-SUP

```
! X &L = &R{a,b}
---------------- DUP-SUP
if L == R:
  X₀ ← a
  X₁ ← b
else:
  ! A &L = a
  ! B &L = b
  X₀ ← &R{A₀,B₀}
  X₁ ← &R{A₁,B₁}
```
