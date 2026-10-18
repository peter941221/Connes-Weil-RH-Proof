# 2883 Route B D4 derivative endpoint identities

The exact derivative polynomial has endpoint factors:

```text
P(0,z)  = 2 - z
P(-1,z) = 128 (z - 1)(z + 1)(9 z^2 - 2)
P(0,2)  = 0
P(-1,1) = 0
```

Thus both outer endpoint cells are zero-margin cells for `P`, explaining why
plain interval boxes do not close them. The proof must use the first nonzero
variation along the owner curve, rather than a strict endpoint value.
