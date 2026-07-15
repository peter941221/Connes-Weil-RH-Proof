# Proof 300: Positive polar readback and one-prime no-gain guard

Date: 2026-07-16

Status: exact identification of Proof 299's positive symmetric first jet with
the route's original normalized projection response.  This is a scalar
readback through the already legal source owner, not a new infinite-dimensional
trace cycle.  An exact two-dimensional one-prime model then proves that a
positive symmetric determinant supplies neither a sign nor the missing extra
Euler half-power.

This does not prove the Sonin Toeplitz covariance estimate, the moving-band
uniform estimate, Gate 3U, the finite-`S` sign, the arithmetic same-object
identity, negative-owner integration, Burnol's all-zero identity, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| normalized polar isometry                     | exact                        |
| original projection response                  | exact source owner           |
| positive symmetric determinant first jet      | same scalar owner            |
| equality mechanism                            | Proof 263/264/299 readback   |
| bare infinite-dimensional polar trace cycle   | still forbidden              |
| positive commuting one-prime guard            | exact                        |
| sign from positivity                           | false                        |
| automatic p^(-1) gain                         | false; response is p^(-1/2) |
| Sonin Toeplitz covariance estimate (AN.13)     | open                         |
| moving-band estimate (AT.18)                  | open                         |
| Gate 3U and RH                                | open / unproved              |
+------------------------------------------------+------------------------------+
```

The logical reduction is

```text
positive symmetric determinant
  -> normalize the killed Gram frame
  -> read its first jet back as the original projection response
  -> test whether positivity itself gives the estimate
  -> exact one-prime guard says no
  -> return to the physical Sonin / moving-band cancellation.       (BK.1)
```

Proof 300 closes an ownership question.  It deliberately does not invent an
estimate from that ownership.

## 2. Normalize the killed Gram frame

Retain Proofs 264 and 299 on `Ran(B)`:

```text
K=E A_S B,
Gamma=K* K>0.                                          (BK.2)
```

Define the normalized polar isometry (polar isometry)

```text
V=K Gamma^(-1/2).                                      (BK.3)
```

Then

```text
V*V=B,
P_S=V V*.                                              (BK.4)
```

The projection `P_S` is the transported band projection which earlier proofs
denoted by `B_S`.  Thus the original diagonal response is

```text
Q_S(g,g)
 =Tr(C_g(P_S-B)C_g*)
 =Tr(W_g(P_S-B)),

W_g=C_g* C_g>=0.                                      (BK.5)
```

The second equality uses the fixed-`S` trace legality already proved in Proof
261.  Equation `(BK.5)` is an ambient completed-boundary trace.  It must not be
replaced by the difference of two separately divergent traces.

## 3. The scalar triangle

Proof 264 gives the ordered Gram owner

```text
Q_S(g,g)
 =Tr_B((K*W_gK-W_B Gamma)Gamma^(-1)).                 (BK.6)
```

Proof 299 uses Hermitian reality to prove

```text
Q_S(g,g)
 =Tr_B(N_sym Gamma^(-1)),                             (BK.7)

N_sym
 =K*W_gK-(W_B Gamma+Gamma W_B)/2.                    (BK.8)
```

It also proves that `(BK.7)` is the first logarithmic derivative of the
positive symmetric determinant:

```text
Q_S(g,g)
 =partial_s log det(R_sym(s))|_(s=0).                 (BK.9)
```

Combining `(BK.5)` and `(BK.9)` gives the exact scalar triangle

```text
                       source trace legality
  Tr(W_g(P_S-B))  <------------------------------+
          |                                       |
          | Proof 264                             | Proof 299
          v                                       |
  Tr_B(N_ord Gamma^-1) ----Hermitian reality----> |
          |                                       |
          +-------------------------------> d log det(R_sym)

  all three vertices equal Q_S(g,g).                       (BK.10)
```

This proves

```text
partial_s log det(R_sym(s))|_(s=0)
 =Tr(W_g(P_S-B)).                                     (BK.11)
```

The proof of `(BK.11)` does not cycle `Gamma^(-1/2)` through two non-trace-
class terms.  It compares two independently legal representations of the same
source scalar.  Therefore Proof 264's unilateral-shift anomaly guard remains
fully active outside this diagonal source first jet.

## 4. Finite normalized determinant coordinate

For algebraic inspection define

```text
P_s=V* exp(sW_g)V,
C_s=B exp(sW_g)B.                                     (BK.12)
```

Both are positive and equal `B` at `s=0`.  Since

```text
G_s=K*exp(sW_g)K
    =Gamma^(1/2)P_s Gamma^(1/2),                      (BK.13)

Gamma_sym(s)=C_s^(1/2)Gamma C_s^(1/2),               (BK.14)
```

finite matrices satisfy

```text
det(R_sym(s))=det(P_s)/det(C_s).                      (BK.15)
```

Differentiating at zero gives

```text
partial_s log[det(P_s)/det(C_s)]|_(s=0)
 =Tr_B(V*W_gV-W_B).                                   (BK.16)
```

In finite dimension `(BK.16)` also equals `Tr(W_g(P_S-B))` by ordinary trace
cyclicity.  The source conclusion is only the scalar identity `(BK.11)`.  The
project has not proved that the two terms in `(BK.16)` are separately trace
class, or that `(BK.15)` is a nonlinear infinite-dimensional determinant
identity.  These stronger statements are unnecessary and remain forbidden.

This distinction is the point:

```text
finite certificate:
  may verify the normalized polar formulas directly;

source theorem:
  obtains the same first-jet scalar through completed-boundary legality;

forbidden inference:
  finite determinant cancellation
    -> unrestricted infinite-dimensional trace cycle.              (BK.17)
```

## 5. Exact positive one-prime guard

The positive determinant is an owner, not an estimator.  This can be proved
without numerical approximation.

On `C^2`, set

```text
U=diag(1,-1),
v=(1,1)/sqrt(2),
B=|v><v|,
T_a=I-aU,
a=p^(-1/2).                                           (BK.18)
```

Here `U` is unitary and self-adjoint.  Normalize the transported line:

```text
v_a=T_a v/||T_a v||
    =((1-a),(1+a))^T/sqrt(2(1+a^2)),

P_a=|v_a><v_a|.                                       (BK.19)
```

Choose either positive detector

```text
W_-=diag(2,1)>0,
W_+=diag(1,2)>0.                                      (BK.20)
```

Both commute with `U`.  Direct substitution into `(BK.19)` gives

```text
Tr(W_-(P_a-B))=-a/(1+a^2),
Tr(W_+(P_a-B))=+a/(1+a^2).                            (BK.21)
```

The associated positive determinant is one-dimensional:

```text
tau_(a,+/-)(s)
 =<v_a,exp(sW_(+/-))v_a>
  /<v,exp(sW_(+/-))v>,                                (BK.22)

partial_s log tau_(a,+/-)(s)|_(s=0)
 =Tr(W_(+/-)(P_a-B)).                                 (BK.23)
```

Equations `(BK.21)--(BK.23)` prove two independent rejections.

First, positivity supplies no sign:

```text
W_->0 gives a negative response,
W_+>0 gives a positive response.                     (BK.24)
```

Second, positivity supplies no extra Euler half-power:

```text
|Q_p|/p^(-1/2)=1/(1+p^(-1)) ->1,

|Q_p|/p^(-1)=sqrt(p)/(1+p^(-1)) ->infinity.          (BK.25)
```

Thus the response is exactly `O(p^(-1/2))`, not `O(p^(-1))`.  The guard is
not a model of the full CC20 Sonin geometry.  It proves that the missing gain
cannot follow from positivity, commutation with the local Euler unitary, polar
normalization, or determinant convexity alone.

## 6. What remains source-specific

The guard sends the route back to the two structures it intentionally omits:

```text
                 +----------------------------------+
                 | complete diagonal Gate 3U owner |
                 +----------------+-----------------+
                                  |
                  +---------------+---------------+
                  |                               |
          +-------v--------+              +-------v--------+
          | fixed-source   |              | synchronized   |
          | Sonin Toeplitz |              | moving band    |
          | covariance     |              | cancellation   |
          +-------+--------+              +-------+--------+
                  |                               |
                  | (AN.13)                       | (AT.18)
                  +---------------+---------------+
                                  |
                         +--------v---------+
                         | compact support  |
                         | before one |.|   |
                         +------------------+                 (BK.26)
```

The fixed-source one-prime target is Proof 277's complete Toeplitz covariance

```text
|Tr(T_(w h_z)^R-T_w^R T_(h_z)^R)|
 <=C(1+z)^(2d)exp(-z/2)||g||_(H^r)^2.                (BK.27)
```

The complete finite-`S` target is Proof 283's moving-band bound

```text
|2 integral_0^1
    partial_(s,r)log ell_(g,g,S,alpha)|_0 d alpha|
 <=C(1+B_root)^d||g||_(H^r)^2.                       (BK.28)
```

Proof 300 does not choose between `(BK.27)` and `(BK.28)` as separate routes.
The recommended attack is to use `(BK.27)` as the local analytic lemma inside
the complete signed moving owner `(BK.28)`.  Taking absolute values between
primes, or between the outer, second-support, and prolate branches, would
discard the cancellation which the two-dimensional guard lacks.

## 7. Finite certificate

`300_positive_polar_no_gain_guard_probe.py` verifies:

```text
V*V=B and P_S^2=P_S;
the normalized covariance identity (BK.13);
the finite positive determinant equality (BK.15);
the ambient, ordered, symmetric, and normalized-polar first jets;
the exact two-dimensional formulas (BK.21);
the positive one-dimensional determinant derivative (BK.23);
the p^(-1/2), rather than p^(-1), scaling in (BK.25).
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/300_positive_polar_no_gain_guard_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/300_positive_polar_no_gain_guard_probe.py \
  --multiplicity 12 --seed 2300 --parameter 0.08 \
  --guard-primes 211,2011,20011,200003,2000003
```

The two cohorts report:

```text
+--------------------------------------------+-------------+-------------+
| diagnostic                                 | default     | alternate   |
+--------------------------------------------+-------------+-------------+
| maximum exact error                        | 7.66e-11    | 9.08e-11    |
| polar isometry error                       | 1.47e-15    | 1.27e-15    |
| finite positive determinant equality       | 7.77e-15    | 6.66e-15    |
| symmetric/polar response error             | 2.94e-15    | 5.26e-15    |
| one-prime response formula error           | 8.78e-16    | 6.86e-16    |
| measured amplitude exponent                | 0.9982      | 0.9991      |
| p^(1/2)-scaled minimum response             | 0.9902      | 0.9953      |
| p-scaled response at largest prime          | 1000.0      | 1414.2      |
+--------------------------------------------+-------------+-------------+
```

The finite source-shaped cohort verifies algebra only.  The two-dimensional
guard is an exact logical counterexample to an automatic positivity estimate;
it is not evidence against a source-specific CC20 cancellation.

## 8. Route judgment

```text
positive symmetric determinant:
  exact diagonal endpoint owner;

normalized polar coordinate:
  exact scalar readback through the source response;

positivity plus local Euler commutation:
  neither sign nor extra half-power;

actual remaining mechanism:
  complete Sonin Toeplitz covariance inside the synchronized moving band.
                                                                    (BK.29)
```

The next proof should stop changing endpoint owners.  It should attack the
source analytic estimate `(BK.27)` and show how its local half-power enters
the complete signed finite-`S` transgression `(BK.28)` without a primewise
absolute value.  Gate 3U, the finite-`S` sign, the arithmetic same-object
identity, negative-owner integration, Burnol's identity, and RH remain open.
No Lean owner or route rewire is authorized.

## 9. Successor: Proof 301

Proof 301 writes the Toeplitz covariance as a two-point finite-difference
distribution and applies the compact root correlation before any mode split:

```text
S_J(w,h)
 =1/2 sum_(x,y)
    (w(x)-w(y))(h(x)-h(y))|J_(x,y)|^2.
```

It then transports this identity to the actual synchronized flow.  Each prime
generator is split only after the moving projections `E_alpha` and `R_alpha`
are present, so every channel retains the complete Euler history.  A static
product cocycle is checked separately but is not the route owner: its
substitution gap is `0.890/0.907` in the two cohorts.

The next analytic target is the combined moving `E/R/K_prol` two-point kernel:
prove boundary-residue cancellation, then shift the compactly supported pairing
to the first source strip and retain one signed scalar through the synchronized
Euler integral.  See
`docs/proofs/301_support_first_two_point_cocycle.md`.
