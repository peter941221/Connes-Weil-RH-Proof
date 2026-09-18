# 1670 — Compressed annular Gram trace interface

The source-compressed annular operator now has the same exact positive-operator
form as its ambient counterpart.  Define

```text
CompressedGram(N,n) = CompressedAnnular(N,n)† * CompressedAnnular(N,n).
```

Its ordinary diagonal trace along the named source basis is exactly the
complexified series of squared compressed annular column norms.  This is the
direct source-owner formulation of the remaining energy obligation; it does
not require passing through an ambient trace estimate.

The theorem is formal and axiom-clean.  It supplies an interface for a future
same-owner positive trace or kernel estimate, but proves neither that uniform
trace bound nor RH.
