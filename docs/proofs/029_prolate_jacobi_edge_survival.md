# Prolate Jacobi Edge Survival

Date: 2026-07-11

Status: the ordinary Christoffel--Darboux variance shortcut is rejected. The
formal `q=0` prolate-edge deformation is non-decaying, but fixed-`q`
resummation remains unresolved. RH status is unchanged.

## 1. Universality Threat

For the degree projection `P_N` onto the first `N` orthogonal polynomials,

```text
norm((1-P_N) f(D) P_N)_HS^2
```

is the variance of a linear statistic in an orthogonal-polynomial
determinantal ensemble. Standard right-limit and mesoscopic CLTs show that
such variances are often universal: analytic multiplicative changes of the
weight do not survive in the leading variance.

Therefore replacing the prolate projection by `P_N` cannot recover the finite
Euler terms. This shortcut is rejected.

Sources:

```text
Breuer--Duits, arXiv:1309.6224
  CLTs from right limits of recurrence matrices.

Breuer--Duits, arXiv:1411.5205
  universality of mesoscopic OPE fluctuations.
```

## 2. Why The Prolate Projection Is Different

The actual projection is the positive spectral projection of

```text
W_(a,lambda)=-D^2+2 pi lambda^2(4N_a+1)-1/4.
```

Its spectral edge occurs at polynomial degree `n` of order `lambda^2`. A
subleading perturbation of the Jacobi coefficients can therefore move the
edge by an order-one number of spectral spacings even when it is negligible
relative to the leading coefficient `a_n~n`.

For the first Euler variation, plan 028 gives

```text
K_L(m,n)=sign(m-n)<e_m,cos(LD)e_n>,
D'_0=[K_L,D].                                             (J.1)
```

Since `D` is tridiagonal and `cos(LD)` preserves parity, the off-diagonal
Jacobi variation has the exact formula

```text
(a_n)'_0
  = a_(n-1)<e_(n-1),cos(LD)e_(n+1)>
    -a_(n+1)<e_n,cos(LD)e_(n+2)>.                         (J.2)
```

Here

```text
a_n=(1/2)sqrt((2n+1)(2n+2))
```

is the exact archimedean coefficient. Formula (J.2) reduces the survival
question to two near-diagonal matrix coefficients of the unitary dilation
`exp(iLD)` in the Hermite/metaplectic basis.

## 3. Source Q-Series Evidence

The 2024 `q`-series paper supplies analytic evidence stronger than the
experiment. With `q=1/p` and

```text
alpha_n=(-4)^(-n) binomial(2n,n),
```

it proves

```text
a_n(q)^2
  =(n+1/2)(n+1)
   (1+2 sqrt(2)(alpha_(n+1)-alpha_n)q+O(q^2)).            (J.3)
```

Since

```text
alpha_n~(-1)^n/(sqrt(pi n)),
alpha_(n+1)-alpha_n~-2 alpha_n,
```

the coefficient of `q` in `a_n(q)` is oscillatory of order `sqrt(n)`. Thus
the first Euler deformation provably survives at the prolate edge at the
level of the source `q` expansion.

Source:

```text
Consani--Moscovici, arXiv:2403.01247,
pqfile1.tex:1510-1542, especially the displayed formula for a(n)^2(q).
```

The remaining caveat is nonuniformity: a Taylor coefficient at `q=0` does not
by itself give fixed-`q` large-`n` asymptotics for `q=1/2`.

## 4. Stable Numerical Cross-Check

`028_jacobi_first_variation_probe.py` evaluates (J.1) by functional calculus
of the exact archimedean Jacobi matrix. Sections 384 and 512 agree at every
displayed index through `n=128`:

```text
n       (a_n)'_0
16       2.9884631879
24      -1.2896635992
32      -2.2652411996
48      -4.1749121265
64       4.8100891272
80       3.5479970637
96      -7.2014333120
128      8.8695237067
```

The deformation is oscillatory and its envelope is compatible with
`sqrt(n)`, not decay to zero. Since `n~lambda^2` at the prolate edge, this is
an order-`lambda` edge phase. The finite Euler perturbation is therefore not
removed by the bulk universality argument.

These numbers do not prove the asymptotic envelope. Their role is to reject
the proposed easy death mechanism and to select the exact analytic target
(J.2).

## 5. Next Analytic Bottom

The operator `exp(iLD)` is the metaplectic squeeze/dilation by `exp L=p`.
Its Hermite matrix coefficients have hypergeometric formulas. The next theorem
must obtain the near-diagonal asymptotic

```text
<e_n,cos(LD)e_(n+2)>
  = n^(-1/2) A_L cos(Phi_L(n)) + O(n^(-3/2)),             (J.4)
```

with an explicit amplitude and phase. Inserting (J.4) into (J.2) determines
the edge scattering phase. The required match is the source phase

```text
u_p(s)=(1-p^(-1/2+is))/(1-p^(-1/2-is)).                  (J.5)
```

The quickest rejection criterion is now explicit:

```text
fixed-q resummation of (J.3) loses its sqrt(n) edge term
  -> prolate escape rejected.

phase/amplitude from (J.2)--(J.4) != logarithmic derivative of (J.5)
  -> prolate escape rejected.
```

If they agree, the first Euler correction survives both the fixed-cutoff
Dirac obstruction and OPE variance universality.

## 6. Verdict

```text
ordinary degree-projection variance: dead by universality.
formal prolate-edge Euler variation: non-decaying.
fixed-q edge survival: unresolved by plan 030.
next owner: fixed-q resummation and squeeze-matrix asymptotic (J.4).
```
