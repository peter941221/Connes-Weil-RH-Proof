# Proof 253: Nested Berezin synchronized flow

Date: 2026-07-15

Status: exact continuous common-carrier reduction and a reproducible
finite-section decomposition certificate.  The synchronized finite-`S` flow
from Proof 252 has an exact nested Berezin formula.  On a compact pre-root its
quadratic form is the difference of two commutator Dirichlet pairings, one for
the transported half-line projection and one for the transported Sonin
projection.  Both the detector multiplier and the Euler generator occur only
through two-point differences.  Hence every scalar part of the complete Euler
generator cancels exactly before an estimate.

A scalar normalization which leaves all transported ranges unchanged also
makes the complete metric at least the identity.  Every compressed metric
inverse, including the nested Schur-complement inverse, then has norm at most
one uniformly in the finite prime set.  The inverse ambient metric is a convex
average of translations with an explicit product-geometric probability law.

These facts remove two artificial sources of growth: the coherent scalar
Euler bulk and the condition number of the compressed inverses.  They do not
yet control the remaining difference-kernel energy uniformly in `S`.  The
finite sections through `p<=997` keep the two Berezin components order one and
of opposite sign, but the values are not a continuous convergence theorem.
No Lean owner or route rewire is authorized, and RH remains unproved.

## 1. Source audit first

CCM24 defines on the real Mellin coordinate

```text
E_S(s)=product_(v in S) L_v(1/2+is)                   (B.1)
```

and equips the common entire-function vector space `B_lambda` with the norm
induced by

```text
L2(R, ds/|E_S(s)|^2).                                 (B.2)
```

The exact source locations in `mainc2m24fine.tex` are:

```text
line 866          definition (B.1)
lines 986--1029   common Sonin carrier and theta_S transport
lines 1033--1073  common entire functions, S-dependent inner product
```

The subsequent paragraph about a Hermite--Biehler structure function is inside
an `\iffalse` block and discusses only `S={infinity}` through Burnol's
archimedean function.  Thus CCM24 does not state that the semilocal structure
function is the Burnol function divided by the Euler multiplier.

This rejects the tempting shortcut

```text
same entire functions + changed Euler weight
  => semilocal kernel is obtained by differentiating an explicit phase.
                                                               (B.3)
```

Burnol gives the explicit evaluator kernel and structure function for the
archimedean Sonin space:

```text
https://arxiv.org/pdf/math/0208121
  equations (1)--(2), Theorems 4 and 8--9.
```

CCM24 proves that the semilocal norm is legitimate, but the new reproducing
kernel must still be computed through the changed metric.

## 2. Complete common-carrier metric

For a finite prime set `S`, put

```text
a_p=p^(-1/2),
L_p=log(p),

tau_(S,t)(s)
 =product_(p in S)(1-t a_p exp(-i L_p s)),
0<=t<=1.                                               (B.4)
```

The sign in the exponential depends only on the fixed translation convention;
none of the real metric formulas below changes under conjugation.

Let `J` be either the archimedean Sonin projection `R` or the crossed half-line
projection `E`, with `R<=E`.  On `Ran(J)` define

```text
H_(S,t)=M_(|tau_(S,t)|^2),
A_(J,S,t)=J H_(S,t) J.                                (B.5)
```

Every local factor is nonzero on the real axis, so `A_(J,S,t)` is boundedly
invertible for finite `S`.  The orthogonal projection onto the transported
range is exactly

```text
J_(S,t)
 =M_(tau_(S,t)) J A_(J,S,t)^(-1) J M_(conj(tau_(S,t))).
                                                               (B.6)
```

If `K_(J,0)(s,u)` is the base projection kernel and `k_(J,0,u)` its evaluator
vector, `(B.6)` gives the common-carrier kernel

```text
K_(J,S,t)(s,u)
 =tau_(S,t)(s) conj(tau_(S,t)(u))
    <A_(J,S,t)^(-1) k_(J,0,u),k_(J,0,s)>.             (B.7)
```

Formula `(B.7)` is the exact nonconstant amplitude omitted by the phase-only
shortcut `(B.3)`.  It is an inverse compressed metric, not a freely chosen de
Branges field.

## 3. Synchronized Berezin derivative

The right logarithmic derivative is multiplication by

```text
x_(S,t)(s)
 :=partial_t log(tau_(S,t)(s))

 =-sum_(p in S)
    a_p exp(-i L_p s)/(1-t a_p exp(-i L_p s))

 =-sum_(p in S)sum_(m>=1)
    t^(m-1)p^(-m/2)exp(-i m L_p s).                   (B.8)
```

Let

```text
k_(J,S,t)(s)=K_(J,S,t)(s,s).                          (B.9)
```

Proof 224 derives the one-prime case.  Its argument uses only the general
projection derivative and therefore gives for the complete multiplier

```text
partial_t k_(J,S,t)(s)

 =2 Re integral_R
    (x_(S,t)(s)-x_(S,t)(u))
    |K_(J,S,t)(s,u)|^2 du.                            (B.10)
```

The projection identity

```text
integral_R |K_(J,S,t)(s,u)|^2 du=k_(J,S,t)(s)         (B.11)
```

is what converts the two raw terms in the projection derivative into the
difference in `(B.10)`.  A scalar generator therefore has zero derivative, as
it must: scalar multiplication does not move a range.

## 4. Exact nested decomposition

Put

```text
B_(S,t)=E_(S,t)-R_(S,t).                              (B.12)
```

It is an orthogonal projection.  Write its kernel as `K_B` and the kernels of
`E_(S,t),R_(S,t)` as `K_E,K_R`.  Since the ranges are nested,

```text
K_E=K_R+K_B.                                          (B.13)
```

Subtract the two copies of `(B.10)`.  With

```text
h_(S,t)=Re(x_(S,t)),                                  (B.14)
```

the diagonal band density `b_(S,t)(s)=K_B(s,s)` satisfies

```text
partial_t b_(S,t)(s)

 =2 integral_R (h(s)-h(u)) |K_B(s,u)|^2 du

  +4 integral_R (h(s)-h(u))
       Re(K_R(s,u)K_B(u,s)) du.                       (B.15)
```

The first line is the band Berezin variance.  The second is the exact
Sonin--band coherence.  It is not an error term: in the finite sections it is
of the same order as the first line and cancels a large part of it.

Equivalently, without expanding the nesting,

```text
partial_t b_(S,t)(s)

 =2 integral_R (h(s)-h(u))
      (|K_E(s,u)|^2-|K_R(s,u)|^2) du.                 (B.16)
```

Equations `(B.15)--(B.16)` are exact continuous identities whenever the
projection kernels and the legally smoothed diagonal traces are defined.  The
companion script verifies them independently of the endpoint calculation.

## 5. Double-difference energy

For one compact smooth pre-root `xi`, put

```text
g=L_+ xi,
L_+=d/dx+1/2,
w(s)=|g_hat(s)|^2.                                    (B.17)
```

The instantaneous nested form is

```text
q_(S,t)(xi)
 =integral_R w(s) partial_t b_(S,t)(s) ds.            (B.18)
```

The kernel difference in `(B.16)` is real and symmetric in `(s,u)`, while
`h(s)-h(u)` is antisymmetric.  Swapping the variables in half of the integral
gives the exact double-difference formula

```text
q_(S,t)(xi)

 =doubleIntegral_R2
    (w(s)-w(u))(h_(S,t)(s)-h_(S,t)(u))
    (|K_E(s,u)|^2-|K_R(s,u)|^2) ds du.                (B.19)
```

Thus the detector and the Euler metric both enter only through differences.
No constant component of either multiplier contributes.

Proof 261 supplies fixed-`S` ordinary trace legality.  Define the extended
trace pairing

```text
D_J(w,h)
 :=Tr([M_w,J]* [M_h,J]).                              (B.20)
```

Here `[M_w,J]` is trace class and `[M_h,J]` is bounded.  If both commutators
belong to `S2`, `(B.20)` agrees with their Hilbert--Schmidt inner product.  The
route does not require that stronger premise.

The commutator kernel is

```text
[M_w,J](s,u)=(w(s)-w(u))K_J(s,u),                     (B.21)
```

so `(B.19)` is precisely

```text
q_(S,t)(xi)
 =D_(E_(S,t))(w,h_(S,t))
  -D_(R_(S,t))(w,h_(S,t)).                            (B.22)
```

This is the new lowest exact owner.  It is a difference of two commutator
Dirichlet pairings, not an absolute sum of prime channels.

Do not apply Hilbert--Schmidt Cauchy--Schwarz to `(B.20)`.  The Euler
multiplier is almost periodic, and its raw half-line commutator need not be
Hilbert--Schmidt.  Proof 261 legalizes `(B.20)` as an `S1`-times-bounded trace
pairing for each fixed finite `S`.  Gate 3U must estimate the signed difference
in `(B.22)`, not the two positive ideal norms.

## 6. Scalar gauge and the uniform metric inverse

Define the positive scalar

```text
c_S(t)=product_(p in S)(1-t a_p)                      (B.23)
```

and replace `tau_(S,t)` by

```text
tauTilde_(S,t)=tau_(S,t)/c_S(t).                      (B.24)
```

This does not change any transported range or projection.  For every real
`s`, each factor obeys

```text
|1-t a_p exp(-iL_p s)|/(1-t a_p)>=1.                 (B.25)
```

Consequently the normalized metric satisfies the operator inequality

```text
Htilde_(S,t)
 :=M_(|tauTilde_(S,t)|^2)>=I.                         (B.26)
```

It follows immediately that

```text
(J Htilde_(S,t) J)^(-1)<=J,

norm((J Htilde_(S,t) J)^(-1))<=1                     (B.27)
```

for `J=R,E`, uniformly in `S` and `t`.

The same bound holds for the nested Schur complement.  In the decomposition
`Ran(E)=Ran(R) direct-sum Ran(B_0)`, write the normalized metric in blocks

```text
[A C]
[C*D]
```

and `Sigma=D-C*A^(-1)C`.  For `b in Ran(B_0)`,

```text
<b,Sigma b>
 =inf_(r in Ran(R)) <r+b,Htilde_(S,t)(r+b)>
 >=||b||^2.                                           (B.28)
```

Hence

```text
Sigma>=I,
norm(Sigma^(-1))<=1.                                  (B.29)
```

This removes the exponentially bad product of the naive one-prime inverse
bounds.  It does not bound the normalized multiplier `tauTilde` by itself;
the isometric combinations in the projection formula must remain whole.

## 7. Positive normalized generator

The scalar gauge changes `h_(S,t)` by a constant, which leaves `(B.15)`,
`(B.19)`, and `(B.22)` unchanged.  For one prime put

```text
r=t a_p,
theta=L_p s.
```

The normalized real generator is

```text
hTilde_(p,t)(s)
 :=partial_t log(
      |1-t a_p exp(-i theta)|/(1-t a_p))

 =a_p(1+r)(1-cos(theta))
   /[(1-r)(1-2r cos(theta)+r^2)]

 =sum_(m>=1)t^(m-1)a_p^m(1-cos(m theta))
 >=0.                                                  (B.30)
```

It vanishes at `s=0`.  Summing over primes gives

```text
hTilde_(S,t)(s)=h_(S,t)(s)-h_(S,t)(0)>=0.             (B.31)
```

At the endpoint the removed scalar bulk is

```text
-h_(S,1)(0)
 =sum_(p in S) a_p/(1-a_p).                           (B.32)
```

For `p<=997`, `(B.32)` is about `16.96`.  It is absent from the exact form
before any estimate.

Metric monotonicity does not imply a projection sign.  Proof 227 proves that a
nonzero instantaneous nested projection derivative has symmetric positive and
negative spectrum.  Equations `(B.26)` and `(B.30)` control inverses and
normalization only; they do not prove `q_(S,t)<=0`.

## 8. Markov inverse

The normalized inverse metric has an additional exact probabilistic form.  For
one local factor,

```text
(1-r)^2/|1-r exp(i theta)|^2

 =(1-r)/(1+r)
   sum_(n in Z) r^|n| exp(i n theta).                  (B.33)
```

The coefficients

```text
P_r(n)=(1-r)/(1+r) r^|n|                              (B.34)
```

are nonnegative and sum to one.  Therefore

```text
Htilde_(S,t)^(-1)
```

is a convex average of translations by random sums

```text
sum_(p in S) N_p log(p),

P(N_p=n)=P_(t a_p)(n),                                (B.35)
```

with independent two-sided geometric variables `N_p`.

This representation is source-free elementary Fourier algebra.  It suggests a
uniform proof through averaged boundary crossings rather than word-by-word
absolute Euler sums.  The compressed inverse is not equal to the compression
of `(B.35)`, so operator Jensen or the Schur owner must be used carefully; the
probability formula alone does not prove the route estimate.

## 9. Finite-section certificate

The companion script uses the exact `log(p)` Fourier translations from Proof
252.  It computes the diagonal derivative in four independent ways:

```text
direct projection derivative;
difference of the two individual Berezin formulas;
band variance plus nested coherence;
difference of the two commutator Dirichlet pairings.   (B.36)
```

It also adds a nonzero complex scalar to `x_(S,t)` and verifies that the result
does not change.  In the default run every density identity has relative error
at most `6.1e-14`, and 12-point integration recovers every endpoint with error
at most `7.7e-10`.

On the fixed compact four-mode pre-root, the default section gives

```text
+--------+--------+---------+---------+----------+-----------+----------+
| p <=   | scalar | D_E     | D_R     | band     | coherence | complete |
+--------+--------+---------+---------+----------+-----------+----------+
|      2 |  2.414 | -4.409  | -2.380  | -4.295   |  2.266    | -2.029   |
|      3 |  3.780 | -4.169  | -1.548  | -3.873   |  1.252    | -2.621   |
|      5 |  4.589 | -4.241  | -2.449  | -4.366   |  2.574    | -1.792   |
|     11 |  5.629 | -4.303  | -2.731  | -4.655   |  3.083    | -1.572   |
|     29 |  7.122 | -4.223  | -2.576  | -4.580   |  2.933    | -1.648   |
+--------+--------+---------+---------+----------+-----------+----------+
```

Here `scalar` is the endpoint bulk `(B.32)`, and `complete=D_E-D_R` is also
`band+coherence`.

At `p<=997`, with 168 prime factors,

```text
scalar bulk       16.956
maximum hTilde    23.267
D_E               -2.378
D_R               -1.629
band variance     -2.763
coherence         +2.014
complete          -0.748.                              (B.37)
```

Thus the legally gauged scalar bulk grows while both exact Dirichlet forms
remain order one in the probe.  At the fixed half-box `10.24`, refinement from
`size=256` to `size=320` changes

```text
band/coherence/complete

from -2.763/+2.014/-0.748
to   -3.169/+2.349/-0.820.                             (B.38)
```

The values are not converged, but the two-component mechanism survives.  This
is diagnostic evidence only.  Finite-rank projection identities and periodic
Fourier sections do not prove a continuous uniform bound.

## 10. What is now closed

The following statements are exact mathematics, not numerical conjectures:

```text
the complete common-carrier metric formula (B.6)--(B.7);
the synchronized Berezin derivative (B.10);
the nested band/coherence identity (B.15);
the double-difference and commutator identities (B.19)--(B.22);
exact deletion of every scalar generator component;
the uniform compressed-inverse bounds (B.27), (B.29);
the positive normalized generator (B.30)--(B.31);
the Markov inverse expansion (B.33)--(B.35).
```

The source audit also closes the phase-only shortcut: CCM24 does not provide a
semilocal Hermite--Biehler structure function.

## 11. New analytic bottom

For the actual resonant negative-owner sequence `xi_n`, define

```text
w_n=|Fourier(L_+ xi_n)|^2,
h_(S_n,t)=Re(partial_t log tau_(S_n,t)).               (B.39)
```

The exact detector-specific remainder is

```text
integral_0^1 [
  D_(E_(S_n,t))(w_n,h_(S_n,t))
  -D_(R_(S_n,t))(w_n,h_(S_n,t))
] dt.                                                  (B.40)
```

The next sufficient theorem is

```text
abs((B.40))
 <=C (1+B_n)^d ||L_+ xi_n||_(H^r)^2,                  (B.41)
```

with `C,d,r` independent of the visible finite set `S_n`.  Proof 249's exact
resonant contraction would then make `(B.40)` tend to zero.

The intended proof must preserve the difference in `(B.40)`.  Bounding
`D_E,D_R`, individual primes, or the band/coherence terms separately can lose
the observed cancellation.  The normalized metric gives three concrete tools:

```text
all compressed inverses are contractions;
hTilde is a sum of positive (1-cos) modes with no scalar bulk;
the ambient inverse metric is a probability average of translations.
```

The remaining hard step is a uniform boundary-crossing estimate for the
complete Dirichlet-form difference, with the compact support of the root used
before the Markov/Euler average.  If that response retains a nonzero bulk
growing faster than any polynomial in `B_n`, the detector-specific route is
rejected.

## 12. Reproduction

Run sequentially in WSL:

```text
python3 -B \
  docs/proofs/253_nested_berezin_synchronized_flow_probe.py

python3 -B \
  docs/proofs/253_nested_berezin_synchronized_flow_probe.py \
  --size 256 --step 0.08 --root-width 0.96 \
  --prime-cutoffs 997 --quadrature-order 8 \
  --max-endpoint-error 2e-4

python3 -B \
  docs/proofs/253_nested_berezin_synchronized_flow_probe.py \
  --size 320 --step 0.064 --root-width 0.96 \
  --prime-cutoffs 997 --quadrature-order 8 \
  --max-endpoint-error 2e-4
```

The relaxed endpoint tolerance in the larger runs applies only to the
eight-point path quadrature.  The pointwise Berezin, nested, commutator, gauge,
metric, and orthogonality identities remain checked near floating-point
roundoff.

## 13. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| CCM24 common vector space / changed norm       | source-backed            |
| explicit semilocal structure function          | absent from source       |
| complete common-carrier metric projection      | exact                    |
| synchronized Berezin derivative                | exact                    |
| nested band/coherence decomposition            | exact                    |
| commutator Dirichlet pairing                   | legal by Proof 261       |
| scalar Euler bulk                              | cancels exactly          |
| normalized compressed metric inverses          | uniformly <=1            |
| normalized inverse Markov representation       | exact                    |
| order-one complete finite-S response           | survives in probe        |
| time-integrated bound (B.41)                   | replaced by endpoint     |
| endpoint two-commutator bound, Proof 262       | open, active Gate 3U     |
| fixed-sign theorem                             | not obtained             |
| same-object finite-S trace identity            | open                     |
| Lean owner or route rewire                     | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 253 removes the opaque nonconstant-amplitude placeholder from the route:
it is the compressed metric inverse in `(B.7)`, with the uniform inverse bounds
`(B.27)--(B.29)`.  Proof 261 supplies ordinary trace legality.  Proof 262 then
integrates `(B.40)` exactly and replaces it by one endpoint pairing of the
outer and Sonin source commutators with the complete dual coframe/graph.  That
endpoint compact-support estimate is the active Gate 3U theorem.  More raw
finite Fourier sections or a guessed semilocal phase do not move the route.
