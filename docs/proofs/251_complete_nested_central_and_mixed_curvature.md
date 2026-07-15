# Proof 251: Complete central gain and mixed-prime curvature

Date: 2026-07-15

Status: exact abstract mixed-projection Hessian and a reproducible finite-section
death test.  The one-prime complete nested first variation has strong evidence
for the extra half-power required by Proof 249.  The new two-prime calculation
finds a more serious obstruction: after the Euler coefficients are inserted,
the mixed curvature has the scale `1/sqrt(p*q)`, not `1/(p*q)`, and remains
indefinite after the two genuine pre-root Mellin rows are imposed.  The same
effect survives fixed smooth Galerkin spaces and one explicit four-mode row
witness.  This does not yet reject the detector-specific route: a continuous
Sonin curvature theorem is still required, and a signed aggregate could cancel
even when termwise absolute summation fails.  No Lean owner or route rewire is
authorized.  RH remains unproved.

## 1. Result first

Proof 250 left one one-prime question.  For `L=log(p)` and
`a=exp(-L/2)`, does the complete nested projection difference gain the second
half-power that the separated central cell lacks?

The complete finite-section probe favors

```text
norm(a * B'_0(L)) = O(exp(-L)) = O(1/p).              (C.1)
```

On the longest stable cohort, `exp(L)*norm(a*B'_0(L))` decreases from about
`0.0255` at `L=6` to `0.0205` at `L=8`.  Zero-extended and periodic
translations give the same extracted trace diagonals.  This is good evidence,
not a continuous theorem.

The semilocal owner contains more than one local factor.  For two translation
lengths `L,M`, the exact mixed Hessian below gives instead

```text
norm(exp(-(L+M)/2) * H_(L,M))
  approximately C(M-L) exp(-(L+M)/2).                 (C.2)
```

At fixed separation `M-L=0.5`, the default finite section gives

```text
C(0.5) = 9.40735...,
fitted slope per L+M = -0.4999999865.
```

Thus the one-prime gain does not extend automatically to mixed primes.

```text
+------------------------------+------------------------------+
| channel                      | observed dressed scale       |
+------------------------------+------------------------------+
| one-prime complete tangent   | p^(-1)                       |
| two-prime mixed curvature    | (p*q)^(-1/2)                 |
| desired absolute mixed bound | (p*q)^(-1)                   |
+------------------------------+------------------------------+
```

## 2. Exact mixed projection Hessian

Let `P` be an orthogonal projection on a Hilbert space, let `Pperp=I-P`, and
let `U,V` be commuting bounded operators.  Define

```text
T_(a,b)=(I-aU)(I-bV),
P_(a,b)=orthogonal projection onto T_(a,b) Ran(P).     (C.3)
```

Near `(a,b)=(0,0)`, the moved range is the graph over `Ran(P)` of

```text
L_(a,b)=Pperp T_(a,b) P [P T_(a,b) P]^(-1).           (C.4)
```

Put

```text
A_U=Pperp U P,
A_V=Pperp V P,

D_(U,V)
 =Pperp U V P
  -Pperp U P V P
  -Pperp V P U P.                                    (C.5)
```

Expanding the inverse in `(C.4)` to mixed order gives

```text
L_(a,b)=-a A_U-b A_V+a b D_(U,V)+O(a^2,b^2).          (C.6)
```

The graph projection has the second-order block expansion

```text
P_graph(L)
 =[I-L*L   L* ] +O(norm(L)^3).
  [L       LL*]
```

Therefore the exact mixed Hessian is

```text
H_P(U,V):=partial_a partial_b P_(a,b) at (0,0)

 =D_(U,V)+D_(U,V)*
  +A_U A_V*+A_V A_U*
  -A_U* A_V-A_V* A_U.                                (C.7)
```

Formula `(C.7)` is self-adjoint.  In finite dimension its trace is zero: the
two off-diagonal graph terms have zero trace, while cyclicity pairs the two
positive-corner Gram terms with the two negative-corner Gram terms.

For nested projections `R<=E`, the transported nested complement is

```text
B_(a,b)=E_(a,b)-R_(a,b),
```

so its mixed Hessian is the same-object difference

```text
H_B(U,V)=H_E(U,V)-H_R(U,V).                           (C.8)
```

No phase/amplitude split, Schur approximation, or stored trace value enters
`(C.8)`.  The companion script verifies `(C.7)--(C.8)` against an independent
QR finite difference.  On the default cohort the ambient relative error is
`4.7e-4`; after the trace diagonal and the pre-root differential, the largest
relative error is `1.3e-6`.

## 3. Post-Q finite-section read-off

The probe uses the same finite scattering section as the one-prime central
diagnostic.  It constructs

```text
E = positive half-line projection,
R = near-Sonin intersection projection,
B = E-R.                                              (C.9)
```

For the ambient Hessian `H_B`, it takes the near-diagonal traces, forms the
Toeplitz convolution matrix on one fixed root interval, and applies the
pre-root differential

```text
L_+=d/dx+1/2.                                         (C.10)
```

The two independent route rows on the pre-root are imposed as

```text
M_0(xi)=0,
M_1(xi)=0.                                            (C.11)
```

The `s=1/2` source row is automatic after `g=L_+ xi`, as proved in Proof 220.

The half-line/Sonin split is especially informative.  For every tested pair,

```text
post-Q norm of H_E(U_L,U_M) = 0,
post-Q norm of H_R(U_L,U_M) = post-Q norm of H_B(U_L,U_M).  (C.12)
```

Thus the mixed channel is not a raw half-line-overlap artifact.  It is carried
by the Sonin/scattering geometry.  Equation `(C.12)` is exact in the tested
finite Toeplitz read-off; its continuous analogue remains to be proved.

## 4. Scaling and sign results

The default zero-extension run uses `size=512`, `step=0.05`, root width one,
and eight fixed Dirichlet modes.  At separation `M-L=0.5` it gives

```text
+---------+---------+------------------+------------------+
| L       | M       | Hessian norm     | dressed norm     |
+---------+---------+------------------+------------------+
| 3.0     | 3.5     | 9.4073479412     | 0.3647624642     |
| 4.0     | 4.5     | 9.4073497110     | 0.1341886367     |
| 5.0     | 5.5     | 9.4073484489     | 0.0493652341     |
+---------+---------+------------------+------------------+
```

Multiplication by `exp((L+M)/2)` returns the Hessian norm in the third column.
Multiplication by `exp(L+M)` grows rapidly.  The mixed Euler coefficient has
therefore supplied the only visible half-power product.

The full constrained root spectrum at `L=3,M=3.5` is

```text
[-9.12123..., +9.39330...].                           (C.13)
```

The fixed eight-mode constrained Galerkin spectrum is

```text
[-7.56480..., +5.41903...].                           (C.14)
```

Both signs survive the genuine rows.  This rules out a sign derived only from
abstract nested-projection geometry, but does not rule out a sign after summing
all primes on one selected detector.

## 5. Fixed physical-mode stress test

Raw full-grid eigenvectors can move into an artificial boundary layer.  The
probe therefore fixes the first eight Dirichlet modes before refining the
scattering section, then imposes `(C.11)` inside that fixed space.

The physical half-domain stays approximately `12.8`:

```text
+--------+------+------------+----------------+----------------+
| step   | size | Sonin rank | Galerkin min   | Galerkin max   |
+--------+------+------------+----------------+----------------+
| 0.050  |  512 |         24 | -7.5648        | +5.4190        |
| 0.040  |  640 |         36 | -8.6248        | +5.2737        |
| 0.030  |  854 |         58 | -6.1177        | +3.9321        |
| 0.025  | 1024 |         78 | -6.4487        | +3.4404        |
+--------+------+------------+----------------+----------------+
```

The values are not a converged continuous spectrum.  Their stable qualitative
content is that a fixed smooth finite-dimensional core remains nonzero and
indefinite while the near-Sonin rank grows.

Zero-extended and periodic translations agree in every displayed digit at
`size=512`.  Tightening the near-Sonin tolerance from `1e-8` to `1e-10` also
leaves the selected rank and results unchanged.

## 6. One explicit row witness

To avoid relying on an optimized eigenvector, the probe reuses Proof 240's
four-mode construction.  On the root interval, put

```text
xi=c_1 phi_1+c_2 phi_2+c_3 phi_3+c_5 phi_5,
c_1=-8/15,
c_3=c_5=1,
```

and choose `c_2` from the exact `M_1` equation.  The identity

```text
c_1/1+c_3/3+c_5/5=0
```

gives `M_0(xi)=0`.  This is one fixed smooth witness, not an eigenvector fitted
at each grid.

At fixed physical half-domain, its sampled values are

```text
+--------+----------------------+---------------------+
| step   | maximum row residual | mixed quadratic     |
+--------+----------------------+---------------------+
| 0.050  | 3.88e-3              | +1.638              |
| 0.040  | 2.19e-3              | +0.797              |
| 0.030  | 1.07e-3              | +1.224              |
| 0.025  | 6.66e-4              | +0.755              |
+--------+----------------------+---------------------+
```

The row quadrature residual decreases under refinement.  The quadratic value
oscillates with the noncommuting finite Sonin limit but stays positive and well
away from zero.  Within each fixed grid it is constant under common translation
to about five or six digits.

This supplies a concrete target for a continuous proof: evaluate the mixed
curvature on one finite-exponential autocorrelation, as Proof 240 did for the
ordinary archimedean kernel.  No spectral convergence theorem is needed once
that integral is identified.

## 7. Conditional route consequence

For a finite place set, the semilocal transport multiplier contains the product
of the local factors.  Distinct primes therefore create the mixed coefficient

```text
a_p a_q=1/sqrt(p*q).                                  (C.15)
```

The explicit Weil main term is additive over prime powers; it has no mixed
`p*q` place channel.  Thus `(C.15)` belongs to the semilocal remainder rather
than the named single-crossing Weil ledger.

The next analytic death theorem is deliberately narrow.  For one fixed
`Delta>0`, one compact interval `I`, and one explicit smooth pre-root `xi`
satisfying `(C.11)`, prove

```text
abs(<xi, Kappa_(L,L+Delta) xi>) >= c > 0
for every L>=L_0.                                     (C.16)
```

Here `Kappa` is the continuous post-Q operator induced by `(C.8)` before the
Euler coefficient is inserted.

If `(C.16)` holds on an open `Delta` interval, then termwise absolute summation
over comparable prime pairs has the wrong density.  For `q/p` in a fixed
interval, each pair has size comparable to `1/p`, while there are on the order
of `p/log(p)` possible `q` values for each large `p`.  The absolute pair total
up to `X` grows on the `X/(log X)^2` scale, rather than a polynomial in
`log X`.  Proof 249's support contraction cannot pay that cost.

This consequence rejects only the absolute route

```text
sum of norms of every mixed place channel.            (C.17)
```

It does not reject either of the following:

```text
the signed aggregate mixed curvature cancels on the selected detector;

the detector is constructed to annihilate the finite bad space of the
complete finite-S compact owner.                      (C.18)
```

Those are the two admissible successors if `(C.16)` is proved.

## 8. Source boundary

Primary sources:

```text
Burnol, Sonine spaces and de Branges evaluators
https://arxiv.org/abs/math/0208121

Connes--Consani, archimedean Weil positivity and Sonin/prolate trace
https://arxiv.org/abs/2006.13771

Connes--Consani--Moscovici, semilocal Sonin transport
https://arxiv.org/abs/2310.18423v2
```

Burnol supplies explicit de Branges structure functions and evaluator kernels.
CC20 supplies the archimedean scattering and Sonin/prolate identities.  CCM24
proves stability of the semilocal Sonin space under enlargement of the finite
place set and records the place-dependent Hilbert norm.  None of these sources
states `(C.7)`, `(C.16)`, or an absolute mixed-prime estimate.  The Hessian is a
new project derivation; the continuous curvature bound remains a project
obligation.

## 9. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/251_complete_nested_central_scaling_probe.py

python3 -B docs/proofs/251_mixed_prime_projection_curvature_probe.py

python3 -B docs/proofs/251_mixed_prime_projection_curvature_probe.py \
  --size 640 --step 0.04 \
  --pairs 3:3.48,3.52:4,4:4.48

python3 -B docs/proofs/251_mixed_prime_projection_curvature_probe.py \
  --size 512 --step 0.05 --shift-mode periodic \
  --pairs 3:3.5,4:4.5,5:5.5
```

The mixed script aborts unless:

```text
the analytic Hessian matches an independent finite difference;
the Hessian is self-adjoint and has the constant-rank trace identity;
the outer half-line post-Q curvature cancels;
the two-row full-grid compression is indefinite;
the fixed smooth Galerkin compression is indefinite;
one distinct-pair Hessian coefficient remains nonzero.                 (C.19)
```

## 10. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| abstract mixed projection Hessian              | exact                    |
| independent QR finite-difference check         | passed                   |
| one-prime complete central p^(-1) scale        | strong diagnostic        |
| mixed dressed (p*q)^(-1/2) scale               | strong diagnostic        |
| outer half-line mixed root channel             | cancels in probe         |
| Sonin mixed root channel                       | survives in probe        |
| two-row sign                                    | indefinite in probe      |
| fixed smooth Galerkin sign                     | indefinite in probe      |
| explicit four-mode row witness                 | nonzero in probe         |
| continuous mixed Sonin curvature theorem       | open, decisive           |
| absolute finite-S remainder smallness          | not established          |
| signed aggregate / resonant bad-space control  | open successors          |
| Lean owner or route rewire                     | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

The next proof should attack `(C.16)` for the four-mode witness using the
Burnol evaluator kernel or CC20's scattering representation.  More large raw
finite sections do not move the route.
