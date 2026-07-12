# 043 Adelic Scalar Compensation Rejection

Date: 2026-07-12

Status: product-formula cancellation rejected by the allowed character lattice.

## Candidate

Move the positive prime-multiplier scalar compensation into the archimedean
place using the global product formula, hoping that all local scalar terms
cancel before the positive trace is formed.

## Exact Obstruction

For the prime multiplier, the sharp scalar cost is

```text
c_p = 2 log(p)/(sqrt(p)+1).
```

Burnol's adelic normalization allows changing local additive characters by a
principal rational `q`.  The local scalar shifts then have the form

```text
log(|q|_v) = v_p(q) log(p)       at finite p,
log(|q|_infinity)                 at infinity,
```

with integer valuations `v_p(q)`, and their total is zero by the product
formula.

The required coefficient `2/(sqrt(p)+1)` is nonintegral and varies with `p`;
it cannot equal `v_p(q)` for any rational `q`.  Allowing arbitrary real local
exponents would leave the principal-idele self-duality class and change the
global explicit formula rather than canceling its remainder.

## Verdict

```text
adelic product formula: exact for integer valuation shifts
required compensation: not a principal-idele shift
global scalar cancellation: rejected
```

Primary source for the allowed character torsor and local-term shifts:

```text
Burnol, The Explicit Formula in Simple Terms, arXiv:math/9810169v2, p. 24
https://arxiv.org/pdf/math/9810169
```

See proof 121.

