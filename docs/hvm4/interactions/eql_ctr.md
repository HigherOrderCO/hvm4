# EQL-CTR

```
(#K{a0,a1...} === #K{b0,b1...})  (same tag)
--------------------------------------- EQL-CTR-MAT
For SUC (1n+): ↑(pred === pred)
For CON (<>): ↑((head === head) & ↑(tail === tail))
Others: (a0 === b0) & (a1 === b1) & ...

(#K{...} === #L{...})  (different tag)
------------------------------------- EQL-CTR-MIS
#0
```
