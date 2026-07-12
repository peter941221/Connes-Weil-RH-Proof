# Fixed-Q Schur--Cayley Phase Verdict

Date: 2026-07-11

Status: the easiest remaining death mechanism is rejected.  At `p=2`, the
full finite Schur complement preserves a `sqrt(n)` Jacobi deformation through
degree 512 and converts the Meixner boundary frequency into the expected
metaplectic Cayley frequency.  This is reproducible numerical evidence, not
the required asymptotic theorem.  RH remains unproved.

## 1. Exact Owner

Consani--Moscovici, Proposition 5.3, writes the two parity blocks as

```text
A_n^+/- (q)
  = +/- 2 sqrt(2) sum_(ell>=0)
      alpha_ell q^(2ell+1)/(1-q^(2ell+1))
      |eta_ell^+/-><eta_ell^+/-|.
```

Source: arXiv:2403.01247, `pqfile1.tex:1024-1094`, especially equations
`lambertrank1g`, `pmzg1`, and `pmzg2`.

Using the exact Meixner Poisson kernel from plan 030 gives every entry without
moment inversion or Gaussian quadrature.  If

```text
s_n(q)=Delta_n(q)/Delta_(n-1)(q),
```

then `s_n` is the last Cholesky pivot, equivalently the last-row Schur
complement of the newly enlarged parity block.  The source recurrence is

```text
a_n(q)^2=(n+1/2)(n+1) s_(n+1)(q)/s_n(q).                 (S.1)
```

## 2. Mandatory Numerical Guard

The source moments carry an overall factor `1-q` relative to the bare
`|L_p|^2` density.  With `a=sqrt(q)`, every normalized finite Gram matrix must
satisfy

```text
(1-a)/(1+a) I <= G_n(q) <= (1+a)/(1-a) I.                (S.2)
```

For `q=1/2`, the admissible interval is `[0.171573,5.82843]`.  Every tested
even and odd block through degree 513 passes (S.2).  At the largest blocks the
smallest eigenvalues are about `0.1764` and `0.1771`, still above the exact
lower bound.  The older unscaled square bounds are false for the source moment
normalization and have been removed from plan 030.

Lambert truncations at 20, 24, 32, and 40 layers agree in the reported
Jacobi deformation to roughly `10^-6` or better through degree 128.

## 3. Schur Survival

The directly computed adjacent pivots give:

```text
n    s_n          s_(n+1)      a_n(q)-a_n(0)   /sqrt(n)
16   0.64545555   0.51575253   -1.77702614      -0.44425653
32   0.55520357   0.67455974    3.34892045       0.59201109
64   0.73027843   0.62377755   -4.90736994      -0.61342124
96   0.63576587   0.72388956    6.48772704       0.66215087
128  0.66594061   0.60684265   -5.84555931      -0.51667933
256  0.62124003   0.64555481    4.97625604       0.31101600
```

The output remains oscillatory at `sqrt(n)` scale.  Therefore the growing
Schur row does not enact the proposed exact cancellation of the fixed-width
Meixner edge wave.

## 4. Cayley Phase

An FFT of the normalized sequence over `64<=n<=512` has dominant angular
frequency near `1.28742`.  The exact source boundary input has frequency
`4 arctan(q)`; the observed output frequency is

```text
omega_p
  = pi-4 arctan(q)
  = 4 arctan((1-q)/(1+q))
  = 4 arctan(tanh(log(p)/2)).                             (S.3)
```

For `p=2`, (S.3) is `1.2870022176`.  This is precisely the Cayley parameter of
the dilation by `p`, expressed in the metaplectic/Hermite coordinate.

Least-squares fits at the exact frequency, including a constant, second
harmonic, and `n^(-1/2)` correction, give:

```text
fit range   main amplitude   second harmonic   residual RMS   max residual
32..512     0.650663         0.012874          0.03371        0.14661
64..512     0.650990         0.012457          0.02730        0.09532
128..512    0.651350         0.011181          0.01935        0.05946
256..512    0.651395         0.009842          0.01007        0.02535
```

The shrinking residual and stable nonzero amplitude reject a chance FFT-bin
match at the tested scales.  They strongly select the theorem

```text
a_n(q)-a_n(0)
  = sqrt(n) A(q) cos(n omega_p+phi(q)) + O(1),
A(q) != 0.                                                (S.4)
```

Equation (S.4) remains a conjectural asymptotic.  The experiment does not
prove its error term or nonvanishing for every prime.

## 5. Route Judgment

```text
fixed-q Meixner boundary wave: proved before Schur transfer.
uniform finite Gram invertibility: proved by density equivalence.
Schur cancellation death mechanism: rejected numerically through n=512.
Cayley/metaplectic phase match: strong numerical evidence.
Schur asymptotic (S.4): open.
semilocal prolate self-adjoint/domain theorem: open.
cross-spectral trace -> Weil distributional limit: open.
RH: unproved.
```

The escape route is now narrower but materially stronger:

```text
Meixner--Lambert exact kernel
  -> Schur--Cayley asymptotic (S.4)
  -> semilocal prolate edge parametrix
  -> positive cross-spectral trace limit
  -> finite-prime Weil phase before scalar D_S appears.
```

The next rejection test is analytic, not larger floating-point numerics:
derive (S.4) from the boundary resolvent or prove that its apparent amplitude
vanishes asymptotically beyond all tested degrees.
