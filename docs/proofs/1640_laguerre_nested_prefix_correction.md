# 1640 — Laguerre nested-prefix correction and producer candidate

Date: 2026-09-18

Status: corrected numerical research record, not a theorem. It serves the
healthy-CompactLog B5 carrier consumer and the formal compact-observable
interface of 1636. The carrier base remains open; RH is not claimed.

## 1. Two implementation corrections

The 1639 table had two independent finite-section defects:

1. the first run used a degree list with gaps;
2. after changing to degrees 0 through 30, it orthogonalized all 31 columns
   and then took the first `dim` columns. Those columns are not the literal
   degree-prefix spaces, because they depend on degrees above `dim`.

The corrected experiment uses the consecutive raw columns
`0, 1, ..., dim-1` at every dimension and solves the generalized Hermitian
problem

```text
M_dim c = sigma_dim^2 G_dim c,

G_dim[i,j] = <H_i,H_j>,
M_dim[i,j] = <P_+(U_lambda H_i), P_+(U_lambda H_j)>.
```

The compact observable is unchanged: the rank-two projection onto the
rational Hardy vectors with spatial profiles `h_3` and `h_4`.

## 2. Corrected readback

At `N = 16384`, `d xi = 1/128`, with degrees 0 through 30:

```text
lambda   dim=8 sigma       dim=10 sigma      dim=12 sigma      dim=14 sigma      observable mass at dim=14
0.2      2.0617e-4         2.0019e-4        1.3160e-4         4.7693e-5         0.9952
0.1      1.5979e-5         2.8835e-6        6.1584e-7         1.5115e-7         0.9225
0.05     3.7223e-6         5.6665e-7        1.0431e-7         1.9267e-8         0.9315
0.02     6.2379e-7         7.7376e-8        1.2248e-8         1.0427e-8         0.9398
```

The independent `N = 32768` candidate extraction agrees at the displayed
digits for the resolved rows. At `lambda = 0.1`, for example, dimensions
8, 10, 12, 14 give `1.5979e-5`, `2.8834e-6`, `6.1587e-7`, and `1.5193e-7`,
with observable masses `0.9494`, `0.9399`, `0.9309`, and `0.9225`.

The model controls remain structurally distinct: for `m = 1, lambda = 1`,
the generalized minimum is `1` at every tested dimension. At `m = 1,
lambda = 0.2`, the same prefix family gives `7.5080e-5` at dimension 14,
so the finite-window model is also resolved rather than being used as a
false zero control.

## 3. What this does and does not establish

This repairs the numerical producer candidate: the spaces are genuinely
nested, the compact observable is fixed, and the minimizing vectors retain
large observable mass while the finite-section defect decreases. It is
evidence for the 1636 interface hypotheses at a fixed scale, not a proof of
their infinite-dimensional limits.

The remaining analytic obligations are unchanged:

1. completeness and normalization of the Laguerre Hardy-side system in the
   committed input space;
2. convergence of the fixed-scale finite-section defects to zero;
3. a positive limiting lower bound for the compact observable;
4. removal of the FFT truncation and the generalized-eigenvector numerical
   conditioning.

No route-map conclusion is changed by this raw numerical correction. In
particular, the carrier base, the Toeplitz producer, and the RH gate remain
open.

## 4. Reproducibility

The corrected main probe is
`scripts/carrier_laguerre_fixed_scale_1639.py`; its candidate/eigenvector
readback is
`scripts/carrier_laguerre_candidate_1640.py`.
