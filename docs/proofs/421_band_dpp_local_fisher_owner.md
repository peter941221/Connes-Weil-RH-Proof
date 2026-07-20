# Proof 421: band DPP local Fisher owner

Date: 2026-07-20

Status: exact finite-dimensional probability owner for the recombined moving
band, together with an infinite-dimensional source audit.  The four-term Gram
determinant of Proof 420 is the log-Laplace transform of a projection
determinantal point process.  More importantly, after the outer and Sonin
spaces are recombined into the actual band, its detector response has a
canonical positive majorant: the detector-pushforward Fisher action of the
band DPP path.

This identifies a concrete positive localized entropy rather than leaving the
symbol `mathfrakE` abstract.  It does not yet construct the infinite Burnol
band DPP limit, bound that Fisher action by the canonical Euler energy, close
Gate 3U, prove the finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+---------------------------+
| layer                                                | judgment                  |
+------------------------------------------------------+---------------------------+
| finite Gram determinant                             | projection-DPP partition  |
| scalar multiplier transport                         | multiplicative DPP tilt   |
| detector response                                    | difference of expectations|
| scalar path square gain                              | Jeffreys/Fisher inequality|
| nested band transport                               | inverse-adjoint frame     |
| generic band density ratio                           | not a scalar product tilt|
| recombined band detector variance                    | root commutator square    |
| detector-pushforward Fisher action                   | positive, canonical       |
| standard infinite DPP weight theorems                | wrong prime-log contract  |
| Fisher-to-canonical-energy estimate                  | open, exact next producer|
| Gate 3U / finite-S sign / Burnol / RH                 | open / open / open / open |
+------------------------------------------------------+---------------------------+
```

The new ownership chain is

```text
actual band `B_t=E-R_t`
  -> projection DPP of `B_t`
  -> regularized compact-root statistic `X_w`
  -> detector-conditional score
  -> positive local Fisher action
  -> canonical Euler energy bound
  -> Gate 3U.                                           (DF.1)
```

Only the last two arrows remain open.  Applying DPP entropy separately to `E`
and `R_t` is invalid and loses the cancellation in `(DF.1)`.

## 2. Projection DPP behind the Gram determinant

Start on a finite ground set `Omega={1,...,N}`.  Let

```text
J : C^r -> C^N                                           (DF.2)
```

be a full-rank frame and put

```text
G_J=J*J,
P_J=J G_J^(-1)J*.                                      (DF.3)
```

For every `r`-element subset `X` of `Omega`, let `J_X` be the square row
minor.  Cauchy--Binet gives

```text
mu_J(X)
 :=abs(det J_X)^2/det(G_J)
  =det((P_J)_(X,X)),

sum_(abs X=r) mu_J(X)=1.                               (DF.4)
```

This is the fixed-size projection DPP of `Ran(J)`.  For a real diagonal
statistic

```text
X_w(X)=sum_(i in X)w_i,                                (DF.5)
```

another application of Cauchy--Binet gives

```text
log E_(mu_J) exp(s X_w)
 =log det(J* exp(s M_w)J)-log det(J*J).                (DF.6)
```

Thus Proof 420's `L_J(I;s)` is exactly the log-Laplace transform of `X_w`.
This is the same Andreief/Cauchy--Binet mechanism used for finite model spaces
in Proof 346, now stated for the nonorthogonal weighted frame required by
Proof 407.

## 3. Scalar multiplier path and the finite square gain

Let `m_i` be nonzero scalars on `Omega`, put `g_i=abs(m_i)^2`, and set

```text
J_g=M_(sqrt(g))J.                                      (DF.7)
```

The two DPP laws obey the exact change of measure

```text
d mu_(J_g)/d mu_J (X)
 =product_(i in X)g_i
   /E_(mu_J)[product_(i in X)g_i].                    (DF.8)
```

Consequently Proof 420's four-term determinant is

```text
Psi_M(m;s)
 =log E_(mu_(J_g)) exp(sX_w)
  -log E_(mu_J) exp(sX_w),                            (DF.9)

Psi_M'(m;0)
 =E_(mu_(J_g))X_w-E_(mu_J)X_w.                        (DF.10)
```

Define the exponential path

```text
d mu_t/d mu_0
 =exp(tY)/E_(mu_0)exp(tY),

Y(X)=sum_(i in X)log(g_i).                            (DF.11)
```

It is again the projection DPP of `M_(g^(t/2))J`.  Standard exponential-family
differentiation gives

```text
d/dt E_(mu_t)X_w=Cov_(mu_t)(X_w,Y),
d/dt E_(mu_t)Y=Var_(mu_t)(Y).                         (DF.12)
```

The second integral is the Jeffreys divergence

```text
mathcalJ(mu_1,mu_0)
 :=D_KL(mu_1||mu_0)+D_KL(mu_0||mu_1)
  =integral_0^1 Var_(mu_t)(Y)dt.                      (DF.13)
```

Cauchy--Schwarz is applied only after the whole path:

```text
abs(E_(mu_1)X_w-E_(mu_0)X_w)^2

 <=[integral_0^1 Var_(mu_t)(X_w)dt]
   mathcalJ(mu_1,mu_0).                               (DF.14)
```

Equation `(DF.14)` is the probability form of Proof 417's valid path
inequality.  The one-factor response can be `O(a)` while the divergence is
`O(a^2)` because the square is outside the completed response.

## 4. The actual band is an inverse-adjoint transport

The Gate owner is not the Sonin DPP alone.  Let `E` now denote a finite Hilbert
carrier, let `R` be a closed subspace, and put

```text
B=E minus-orthogonal R.                                (DF.15)
```

For an invertible `A:E->E`, transport the Sonin range to `A R`.  Its actual
orthogonal complement is

```text
B_A=(A R)^perp=A^(-*)B.                               (DF.16)
```

Indeed,

```text
x perp A R
 <-> A* x perp R
 <-> A* x in B
 <-> x in A^(-*)B.                                    (DF.17)
```

In the Fourier/Hardy coordinate of Proof 375, the Euler multiplier preserves
the outer Hardy carrier.  Therefore `(DF.16)` is the literal band transport
with

```text
A=T_(tau_t)|_(H^2).                                   (DF.18)
```

Although `tau_t` is scalar on boundary `L2`, its analytic Toeplitz restriction
to `H^2` is generally nonnormal.  Hence

```text
A^(-*)B != A^(-1)B                                   (DF.19)
```

in general.  The DPP density ratio of `B_A` relative to `B` is then a ratio of
Slater minors,

```text
abs det((A^(-*)J_B)_X)^2/abs det((J_B)_X)^2,          (DF.20)
```

not a product `product_(i in X)g_i`.  This is the probability version of Proof
255's dual coframe and Proof 264's trace anomaly.  Replacing `(DF.16)` by a
scalar inverse weight would erase the same response rejected in Proof 419.

## 5. Canonical detector-localized Fisher action

Let `B_t` be any differentiable finite-rank band path and let `mu_t` be its
projection DPP.  For configurations of nonzero probability define the score

```text
sigma_t(X)=partial_t log mu_t(X),
E_(mu_t)sigma_t=0.                                    (DF.21)
```

For a frame `J_t` of `B_t`, the score is explicitly

```text
sigma_t(X)
 =2 Re Tr(J_(t,X)^(-1) dot(J)_(t,X))
  -Tr[(J_t*J_t)^(-1)partial_t(J_t*J_t)].              (DF.22)
```

The full Fisher information `E sigma_t^2` can diverge in the continuous Euler
problem.  The detector sees only the statistic `X_w`.  Project the score onto
that observable:

```text
sigma_(t,w)
 :=E_(mu_t)[sigma_t | X_w],

I_(t,w)
 :=E_(mu_t)[sigma_(t,w)^2].                           (DF.23)
```

This definition is canonical: conditional expectation is the orthogonal
projection in `L2(mu_t)`.  It gives

```text
d/dt E_(mu_t)X_w
 =E_(mu_t)[(X_w-E X_w)sigma_(t,w)],                   (DF.24)

abs(d/dt E_(mu_t)X_w)^2
 <=Var_(mu_t)(X_w) I_(t,w).                           (DF.25)
```

For a projection DPP,

```text
Var_(mu_t)(X_w)
 =1/2 sum_(i,j)(w_i-w_j)^2 abs(B_t(i,j))^2
 =1/2 norm([M_w,B_t])_2^2.                            (DF.26)
```

Integrating `(DF.25)` once more gives the endpoint inequality

```text
abs(E_(mu_1)X_w-E_(mu_0)X_w)^2

 <=[1/2 integral_0^1 norm([M_w,B_t])_2^2dt]
   mathfrakI_w(B_bullet),                             (DF.27)

mathfrakI_w(B_bullet)
 :=integral_0^1 I_(t,w)dt.                            (DF.28)
```

The quantity `(DF.28)` is the detector-pushforward Fisher action.  It is the
promised positive localized completion: the actual band is formed first, and
only the part of the otherwise divergent score visible to the compact-root
detector is retained.

## 6. The detector factor is already controlled

Proof 375 identifies every transported Sonin range as nearly invariant.  Proof
376 gives, for the Cayley detector coefficient functional `A(w)`,

```text
norm([M_w,R_t])_2<=sqrt(2)A(w),
norm([M_w,E])_2  <=sqrt(2)A(w).                       (DF.29)
```

Since `B_t=E-R_t`,

```text
1/2 norm([M_w,B_t])_2^2<=4A(w)^2.                    (DF.30)
```

Proof 377 bounds `A(w)` polynomially by the compact-root support and Sobolev
norms.  Therefore `(DF.27)` reduces the near Gate to one positive theorem:

```text
mathfrakI_(w_F)(B_bullet)
 <=C_lambda (1+B_F)^d E(S_F),                         (DF.31)
```

or the same bound along the resonant Yoshida sequence.  Proof 416 already
gives

```text
E(S_F)<=C(1+B_F)^2.                                   (DF.32)
```

Equations `(DF.27)--(DF.32)`, together with Proof 336's far lane, would prove
the canonical Gate 3U bound.  Unlike a bare `mathfrakE`, `(DF.28)` specifies
the probability space, path, localization, and positivity that must be
constructed in the continuous limit.

## 7. Why standard infinite DPP entropy does not supply `(DF.31)`

Bufetov's ordinary multiplicative-functional theorem assumes, among other
conditions, a trace-class weighted projection.  Bufetov--Qiu's regularized
version starts from the positive Dirichlet variance

```text
Var(P,f)
 =1/2 doubleIntegral
   abs(f(s)-f(u))^2 abs(K_P(s,u))^2 ds du.            (DF.33)
```

Their Theorem 4.1 also assumes that every set

```text
{s:abs(g(s)-1)>=epsilon}                              (DF.34)
```

is bounded.

Already one Euler factor

```text
g_a(s)=abs(1-a exp(-i ell s))^2                       (DF.35)
```

is nonconstant periodic, so `(DF.34)` fails.  The corresponding logarithm

```text
h_a(s)=log g_a(s)                                     (DF.36)
```

also has infinite sharp-Hardy Dirichlet variance.  Off the diagonal, the
Hardy kernel has magnitude proportional to `abs(s-u)^(-1)`.  On a square
`[-T,T]^2`, change variables to center `x=(s+u)/2` and difference `y=s-u`.
For a positive-measure set of `y`,

```text
x -> abs(h_a(x+y/2)-h_a(x-y/2))^2/y^2                (DF.37)
```

is nonzero periodic with positive mean.  Its integral in `x` grows linearly
with `T`.  Hence the truncated form `(DF.33)` tends to infinity.

This recovers the continuous-multiplicity obstruction of Proofs 253, 260,
261, and 346.  Applying separate positive variances to `E` and `R_t` is both
illegal and structurally wrong: Gate owns the signed difference

```text
D_E(w,h)-D_R(w,h),                                    (DF.38)
```

which becomes legal only after band/root completion.  The standard DPP
theorems do not perform that recombination.

The audit does not reject `(DF.28)`.  A locally trace-class or regularized DPP
for the already recombined band can exist even when the two sea projections
in `(DF.38)` have infinite separate variance.  Establishing that limit and
then proving `(DF.31)` is the new source task.

## 8. Primary-source boundary

The exact external contracts used above are:

```text
Alexander Bufetov,
Infinite Determinantal Measures and the Ergodic Decomposition of Infinite
Pickrell Measures I,
Propositions B.3--B.4,
https://arxiv.org/abs/1312.3161

Alexander Bufetov and Yanqi Qiu,
Determinantal Point Processes Associated with Hilbert Spaces of Holomorphic
Functions,
equations (25)--(29), Theorem 4.1, and Proposition 7.6,
https://arxiv.org/abs/1411.4951
```

Bufetov's Proposition B.4 proves that a legal scalar multiplicative tilt gives
the projection onto `sqrt(g)L`.  It does not cover the inverse-adjoint band
frame `(DF.16)`.  Bufetov--Qiu construct regularized multiplicative
functionals when the stated variance and tail hypotheses hold; they do not
state a relative theorem for the almost-periodic outer-minus-Sonin sea.

## 9. Finite certificate

The companion script enumerates every fixed-size configuration.  It checks:

```text
the projection-DPP probability and Cauchy--Binet normalization;
the Gram log-Laplace formula `(DF.6)`;
the scalar density law `(DF.8)`;
the detector derivative `(DF.10)`;
the covariance and Jeffreys identities `(DF.12)--(DF.14)`;
the inverse-adjoint complement identity `(DF.16)`;
failure of the scalar inverse and scalar-product density replacements;
the score identity `(DF.24)`;
conditional Fisher contraction;
the commutator variance identity `(DF.26)`;
the integrated band inequality `(DF.27)`.
```

Run from the WSL2 ext4 verification mirror:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/421_band_dpp_local_fisher_owner_probe.py
```

The default and alternate WSL2 cohorts reported:

```text
+------------------------------------------+---------------+---------------+
| diagnostic                               | default       | alternate     |
+------------------------------------------+---------------+---------------+
| maximum exact identity error             | 6.93e-16      | 2.55e-15      |
| wrong inverse projection gap             | 3.43e-1       | 2.22e-1       |
| nonmultiplicative density residual        | 8.55e-1       | 6.19e-1       |
| conditional Fisher contraction slack     | 1.70e-1       | 1.59e-1       |
| integrated Fisher bound slack             | 1.99e-3       | 1.40e-3       |
+------------------------------------------+---------------+---------------+
```

Finite enumeration proves only the finite probability algebra.  The
continuous divergence verdict is the periodic calculation `(DF.35)--(DF.37)`,
not a numerical extrapolation.

## 10. Decision

```text
finite weighted determinant as DPP partition:       exact;
finite scalar entropy square gain:                  exact `(DF.14)`;
actual band transport:                              inverse-adjoint `(DF.16)`;
scalar multiplicative law for generic band:         rejected;
positive detector-localized Fisher owner:           exact finite `(DF.28)`;
detector variance factor:                            closed by Proofs 376--377;
standard infinite DPP theorem import:               rejected by hypotheses;
continuous band DPP/Fisher construction:            open;
Fisher-energy estimate `(DF.31)`:                   open, active near producer;
Gate 3U / finite-S sign / Burnol / RH:               open / open / open / unproved.
```
