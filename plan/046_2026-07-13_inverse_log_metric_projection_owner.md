# 046 Inverse-Log Metric Projection Owner

Date: 2026-07-13

Status: rejected by proof 206. The positivity bound is correct, but the
compressed inverse leaks another one-step prime crossing at order `a^2`.

## Candidate

For a finite prime set `S_f`, define

```text
ell_S = sum_(p in S_f) log((I-p^(-1/2)U_p)^*(I-p^(-1/2)U_p)),
b_S = sum_(p in S_f) 2 log(1+p^(-1/2)),
H_S = ((1+b_S)I-ell_S)^(-1).
```

The bound `ell_S<=b_S I` gives `0<H_S<=I`. Let `R_S` be the orthogonal
projection onto `H_S^(1/2) Ran(R)`.

## Proposed split

The positive trace `Tr(C_g R_S C_g^*)` has archimedean bulk
`Tr(C_g R C_g^*)`. Its finite-place factor is

```text
Q H_S R(R H_S R)^(-1).
```

Separating words syntactically by an additional internal `Q` selects

```text
Q(I-H_S^(-1))R
  =Q ell_S R
  =-sum_(p,m) p^(-m/2)/m * Q(U_p^m+U_p^(-m))R.
```

This formal subseries has the desired `1/m` coefficients. It is not the
intrinsic one-crossing part of the positive owner.

## Rejection

The exact block inverse is

```text
Q H_S R(R H_S R)^(-1)
  =((1+b_S)Q-Q ell_S Q)^(-1)Q ell_S R.
```

For one prime, `a=p^(-1/2)`, its difference from `Q ell R` is

```text
a^2(2Q(U+U*)R+Q(U+U*)Q(U+U*)R)+O(a^3).
```

The odd one-step block cannot cancel against the even two-translation word.
On the `log(p)` fiber decomposition it has infinite multiplicity, so the
claimed two-boundary trace-ideal factorization is false. See proof 206.

## Decision

```text
positive metric: retained as an operator fact
exact finite-prime owner: rejected
weighted Wiener gate: not reached
route consumer changes: none
Lean owner: forbidden
```

The exact translation-invariant regression repair is separately rejected by
proof 207 and Plan 047. Plan 032 remains open at Gate 3.
