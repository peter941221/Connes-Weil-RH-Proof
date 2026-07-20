# Proof 409: Burnol near weighted-gradient screen

Date: 2026-07-19

Status: historical diagnostic screen for the near part of the Proof 407
weighted owner.  It uses the actual Burnol boundary moment from the even
cosine transform on `[0,1]` and a fixed-order approximation of the complete
normalized Euler inverse metric.  Proof 411 shows that the far cosine tail is
under-resolved, so the displayed response rows are not certified numerical
evidence.  No continuous estimate, Gate 3U premise, or RH conclusion is
stored.

## 1. Screened object

For the Burnol boundary synthesis map `A`, define

```text
M(z)=A* U_z A,
G=M(0).
```

For a normalized finite Euler inverse metric

```text
M_S = integral U_z d nu_S(z),
G_S = integral M(z) d nu_S(z),
```

and a compact `Q`-completed detector `F=Q phi`, the same-object boundary
response is

```text
Tr[G_S^(-1) integral_z integral_u
       F(u) M(z+u) du d nu_S(z)
   -G^(-1) integral_u F(u) M(u) du].                (BN.1)
```

This is Proof 341's inverse-after-average owner, restricted to the near
displacements.  The source moment is not replaced by a periodic shift model.

## 2. Euler law used by the screen

For one normalized factor with `a=p^(-1/2)`, the signed geometric difference
law is

```text
nu_p(m log p) = rho_p a^|m|,
rho_p=(1-a)/(1+a),
```

and the finite-set law is the convolution of these factors.  The probe truncates
each geometric tail at a declared power and bins only the displacement grid;
it reports the omitted probability mass.  It does not claim that this
truncation is a proof of the infinite law.

## 3. Near split and output

For root radius `B_root`, the displayed near screen keeps

```text
|z| <= 4 B_root + 4
```

and applies no absolute value to the two Burnol Schur terms separately.  It
reports:

```text
near probability mass;
weighted response and response / root Sobolev proxy;
Gram condition number;
finite-section convergence across Burnol Galerkin sizes;
geometric-tail omission bound.
```

The far complement is not estimated by this file; Proof 336 owns that lane at
the route-evidence level.

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/409_burnol_near_weighted_gradient_screen.py
```

## 4. Interpretation rule

```text
stable across size and quadrature + bounded prime-set response:
  only a provisional screen; the complete metric positivity audit must pass;

growth after size refinement or a nonzero cluster lower bound:
  obstruction evidence against the current owner;

either result:
  not a continuous proof until the far oscillatory metric, geometric tails,
  and Schur inverse are controlled with error bounds.
```

## 5. Route judgment

```text
actual non-periodic Burnol carrier       tested;
complete inverse-after-average owner     tested approximately;
near weighted response                   diagnostic only;
continuous root-relative gradient        open;
Gate 3U / RH                             open / unproved.
```

## 6. Proof 411 correction

Proof 411 audits the complete-metric assembly used by this screen.  The far
cosine blocks have frequency `2 pi exp(abs(z))`, while the screen keeps a
fixed Gauss-Legendre order.  At the default finite cohort the resulting
averaged matrix has a large Hermitian defect and negative eigenvalues even
though the exact inverse metric is positive Hermitian.  The response also
changes materially with the quadrature order.

Therefore the numerical rows above are retained as historical output only;
they are withdrawn as survivor or obstruction evidence.  A valid screen must
first evaluate the far metric with an error-controlled oscillatory method (or
use the analytic half-density/far-tail owner) and only then invert the
complete average.  See
`docs/proofs/411_burnol_far_quadrature_audit.md`.
