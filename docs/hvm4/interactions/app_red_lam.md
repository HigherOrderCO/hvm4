# APP-RED-LAM

```
((f ~> λx.g) a)
--------------- APP-RED-LAM
x ← a
(f x) ~> g
Note: we substitute x with a, then return (f (Var x)) ~> g
which effectively becomes (f a) ~> g[x:=a]
```
