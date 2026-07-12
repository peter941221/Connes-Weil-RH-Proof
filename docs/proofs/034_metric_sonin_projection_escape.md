# Metric Sonin Projection Escape

Date: 2026-07-12

Status: an exact source-backed semilocal positive trace has been constructed
without a semilocal prolate self-adjoint extension and without a large-cutoff
cross-spectral limit. The remaining fixed-`S` trace remainder is open. RH
remains unproved.

## 1. Why This Is A Different Theta Route

The rejected biorthogonal route paired `theta_S` with its dual `eta_S`:

```text
<theta_S f,eta_S g>=<f,g>.
```

That pairing cancels the finite Euler factor and transports only the
archimedean trace. The new route uses `theta_S` twice, through the orthogonal
projection onto its image. Since `theta_S` is not unitary, the metric operator
`theta_S* theta_S` remains in that projection and retains arithmetic.

## 2. Exact Source Metric

CCM24 proves that for every support parameter `lambda`,

```text
theta_S : Sonin_lambda(infinity) -> Sonin_lambda(S)
```

is a bounded isomorphism with bounded inverse:

```text
mainc2m24fine.tex:946-1029,
especially tensorsonin1, groundstatedual, and Theorem isosonin.
```

Source: https://arxiv.org/abs/2310.18423

For `S={infinity,p}`, in the multiplicative Fourier coordinate,

```text
T_p:=theta_p,
(T_p f)^(s)=B_p(s) f^(s),
B_p(s)=1-a exp(-iLs),
a=p^(-1/2), L=log(p).                                   (M.1)
```

This is CCM24 `mainc2m24fine.tex:946-981`. Therefore

```text
H_p:=T_p* T_p
   = |B_p(D)|^2
   = (I-aU_p)(I-aU_p*)
   = (1+q)I-a(U_p+U_p*),                                (M.2)

q=1/p, U_p=exp(-iLD).
```

The bounds

```text
(1-a)^2 I <= H_p <= (1+a)^2 I                           (M.3)
```

are exact. For several finite primes, the factors commute and
`H_S=product_p H_p` has the corresponding product bounds.

The Poisson Gram operator from plan 032 is, up to its scalar normalization,
the inverse metric:

```text
G_p=(1-q)H_p^-1.                                        (M.4)
```

Thus the Schur--Wiener--Hopf object at Gate 1 and the semilocal Sonin metric at
Gate 2 are two orientations of the same Euler operator.

## 3. Orthogonal Projection Onto The Semilocal Sonin Space

Let `R_lambda` be the archimedean orthogonal Sonin projection and define

```text
A_(S,lambda)
  := R_lambda H_S R_lambda | Ran(R_lambda).              (M.5)
```

By (M.3), `A_(S,lambda)` is positive and boundedly invertible on the
archimedean Sonin space. The orthogonal projection onto the semilocal Sonin
space `T_S Ran(R_lambda)` is exactly

```text
R_(S,lambda)
  = T_S R_lambda A_(S,lambda)^-1 R_lambda T_S*.          (M.6)
```

Proof: the right side is self-adjoint, fixes every vector `T_S R_lambda x`,
and annihilates its orthogonal complement. Formula (M.6) is the standard
closed-range projection formula, but every factor here is source-owned.

This construction does not mention a formal semilocal prolate operator. CCM24
already proves that `T_S Ran(R_lambda)` is exactly the semilocal Sonin space.

## 4. Positive Trace And Trace-Class Inheritance

Let `C_S(g)` be the integrated semilocal scaling representation for the fixed
test `g`. Formula (M.1) is a scaling convolution/multiplier, so

```text
C_S(g) T_S = T_S C_infinity(g).                          (M.7)
```

Define the source-shaped positive trace

```text
Pos_(S,lambda)(g)
  := Tr(C_S(g) R_(S,lambda) C_S(g)*).                    (M.8)
```

For a convolution square this is the exact analogue of the CC20 Sonin trace,
not a cross-spectral transition. Substituting (M.6)--(M.7) and cycling only
bounded/trace-class factors gives the archimedean-metric expression

```text
Pos_(S,lambda)(g)
  = Tr(
      C_infinity(g) R_lambda A_(S,lambda)^-1 R_lambda
      C_infinity(g)* H_S
    )
  >= 0.                                                  (M.9)
```

Positivity is clearer in (M.8); (M.9) is the arithmetic read-off coordinate.

CC20 proves that the relevant archimedean Sonin-compressed test operator is
Hilbert--Schmidt/trace-class for compact smooth tests. The extra factors in
(M.9), namely `H_S` and `A_(S,lambda)^-1`, are bounded by (M.3). Therefore the
trace-class gate is inherited once the same CC20 factorization is written
before cyclic permutation. No infinite-dimensional prolate spectral
projection or Galerkin limit is needed.

## 5. Arithmetic Does Not Cancel

If `R_lambda` commuted with `H_S`, the compressed inverse in (M.6) would
cancel and the trace would reduce to the archimedean one. Sonin space is not
preserved by scaling, so

```text
[R_lambda,U_p] != 0,
```

and the finite Euler metric remains in

```text
(R_lambda H_S R_lambda)^-1.                              (M.10)
```

This is precisely the half-space Wiener--Hopf compression selected in Gate 1.
The old theta/eta cancellation does not apply to (M.6).

## 6. Remaining Fixed-S Theorem

CC20 proves at the archimedean place

```text
Tr(C_infinity(f)R_lambda)
  = W_infinity(f)+E_infinity,lambda(f),                  (M.11)
```

and controls `E_infinity,lambda o Q` to obtain the Weil lower bound. The new
route requires the fixed-`S` analogue

```text
Pos_(S,lambda)(g)
  = QW_S(g,g)+E_(S,lambda)(g),                           (M.12)

E_(S,lambda)(g) <= 0                                    (M.13)
```

on the same support and vanishing subspace, with the sign adjusted to the
project convention.

The new remainder is not arbitrary: substituting

```text
H_p=(1+q)I-a(U_p+U_p*)
```

into (M.9) gives an explicit compressed Wiener--Hopf resolvent. The first
rejection test is whether its post-`Q` remainder still contains the raw
noncompact finite-Euler translation block found in plans 025--026. If that
block survives without cancellation by `A_(S,lambda)^-1`, the metric escape is
dead. If the compressed inverse cancels it, this is the missing pre-read-off
cancellation theorem that the direct scalar route lacked.

## 7. Route Effect

```text
formal semilocal prolate self-adjointness: bypassed.
positive/negative cross trace: bypassed.
large-lambda continuous-to-Dirac limit: bypassed.
same-test positivity: exact by the orthogonal projection (M.6).
trace-class inheritance: reduced to the CC20 Sonin factorization plus bounds.
finite-prime visibility: retained by the compressed metric inverse.
remaining bottom: sign/ideal class of the explicit fixed-S remainder (M.12).
RH: unproved.
```

The immediate attack is `S={infinity,2}` and one support interval. Expand the
resolvent in (M.10), derive the exact first Euler correction to (M.11), and
test whether the central `p^-1 log(p)` obstruction cancels before `Q`.

This first rejection test now passes algebraically. Expanding the metric
projection to second order gives off-diagonal first variation
`-QUR-RU*Q` and diagonal second variation `diag(-J*J,JJ*)`, where `J=QUR`.
The raw scalar `a^2 I` cancels against the inverse compressed metric before
read-off. See `docs/proofs/035_metric_projection_second_variation.md`. The
remaining test is the smoothed defect-pair sign and the `U^2`/`p^2` atom.
