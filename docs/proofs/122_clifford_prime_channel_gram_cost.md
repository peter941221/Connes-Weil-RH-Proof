# 122 Clifford Prime Channel Gram Cost

Date: 2026-07-12

## Finite PSD Lemma

For a real vector `w` and block matrix

```text
G = [ c  w^T ]
    [ w   I  ],
```

positive semidefiniteness implies, by the Schur complement,

```text
c - w^T w >= 0.
```

This is the finite-dimensional form of the Cauchy--Schwarz cost of realizing a
signed linear form inside a positive square.  Replacing `I` by a positive
matrix `C` changes the bound to `c >= w^T C^(-1)w`; making `C` large is an
explicit diagonal compensation, not a cancellation.

For prime first channels `w_p=log(p)/sqrt(p)`, the Euclidean cost is unbounded
as the visible set grows, since `sum_p log(p)^2/p` diverges.  Anticommuting
Clifford generators realize the block Gram algebra but cannot evade this PSD
inequality.

If one uses a spinor state with zero expectation on every `Gamma_p`, the linear
prime terms disappear.  A state retaining them has a nonzero coupling vector
and is subject to the same Schur bound.

## Verdict

```text
Clifford mixed-word cancellation: valid algebra
positive same-object signed read-off: impossible without growing diagonal cost
cofinal finite-S owner: rejected
RH: unproved
```

