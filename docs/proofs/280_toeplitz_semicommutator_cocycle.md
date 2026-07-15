# Proof 280: Toeplitz semicommutator Fredholm cocycle

Date: 2026-07-15

Status: exact fixed-`S` continuous Fredholm determinant domain for the
two-parameter Toeplitz covariance, together with its finite Burnol-boundary
coordinate.  The detector-first multiplicative semicommutator differs from the
identity by one completed boundary crossing.  Proof 261's trace-class detector
commutator therefore makes its determinant genuine without an ambient
determinant and without any trace-ideal premise on the second multiplier.

The mixed logarithmic derivative is exactly the Proof 277 covariance.  For
`R<=E`, the quotient of the two cocycles owns `S_E-S_R`; in finite boundary
coordinates it is the multiplicative second difference of Proof 279's complete
Burnol relative determinant.  This closes the determinant-domain part of the
successor, not the uniform polynomial-support estimate, the complete prime
stopping theorem, Gate 3U, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| detector-first completed crossing identity    | exact                        |
| fixed-S semicommutator Fredholm determinant   | exact                        |
| mixed derivative is Toeplitz covariance       | exact                        |
| relative E/R determinant line                 | exact                        |
| Burnol multiplicative boundary cross-ratio    | exact finite coordinate      |
| Proof 279 channel-Schur cross-ratio            | exact finite coordinate      |
| ambient determinant                            | unnecessary                  |
| separate infinite boundary determinants       | forbidden                    |
| uniform polynomial-support estimate           | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The ownership change is

```text
raw compressed determinants
  -X-> may not exist individually;

detector-first Toeplitz semicommutator
  -> identity plus one S1 boundary crossing
  -> genuine Fredholm determinant
  -> Burnol boundary multiplicative cross-ratio
  -> complete mixed covariance.                              (AQ.1)
```

## 2. Detector-first cocycle

Let `J` be an orthogonal projection and write

```text
T_J(X)=J X J|_(Ran J).                                (AQ.2)
```

Let `W,H` be bounded commuting self-adjoint operators.  Put

```text
U_s=exp(sW),
V_t=exp(tH).                                           (AQ.3)
```

For real parameters, all three Toeplitz compressions below are positive and
invertible.  They remain invertible in a complex neighborhood of zero.  Define

```text
K_J(s,t)
 =T_J(U_s V_t) T_J(V_t)^(-1) T_J(U_s)^(-1).           (AQ.4)
```

The order in `(AQ.4)` is part of the theorem.  Compare the product compression
with the product of the two compressions:

```text
T_J(U_s V_t)-T_J(U_s)T_J(V_t)
 =J U_s(I-J)V_t J.                                    (AQ.5)
```

Hence

```text
K_J(s,t)-I
 =J U_s(I-J)V_tJ
   T_J(V_t)^(-1)T_J(U_s)^(-1).                        (AQ.6)
```

Equation `(AQ.6)` is the completed crossing factorization.  It is an operator
identity on `Ran(J)`, not only a determinant equality.

## 3. Fixed-S trace-class domain

Proof 261 gives the route contract

```text
[W,J] in S1,       J in {E,R}.                        (AQ.7)
```

Duhamel's formula gives

```text
[U_s,J]
 =integral_0^s exp(rW)[W,J]exp((s-r)W)dr in S1.       (AQ.8)
```

The crossing in `(AQ.5)` satisfies

```text
J U_s(I-J)=-J[U_s,J](I-J) in S1.                     (AQ.9)
```

All other factors in `(AQ.6)` are bounded locally in `(s,t)`.  Therefore

```text
K_J(s,t)-I in S1                                     (AQ.10)
```

trace-norm continuously near the origin, and

```text
c_J(s,t)=det(K_J(s,t))                                (AQ.11)
```

is a genuine Fredholm determinant.

Only the detector-side commutator `(AQ.7)` is used.  No Schatten premise is
placed on `[V_t,J]`.  This is why the detector-first ordering in `(AQ.4)` is
mandatory.  Reversing it would move the trace-class obligation to the raw
Euler/generator leg and would not match Proof 253's extended `S1 x bounded`
pairing.

The second leg `V_t` may therefore retain a complete bounded fixed-`S`
multiplier.  It need not be expanded into prime factors to define `(AQ.11)`.

## 4. Mixed derivative readback

The cocycle is normalized on both coordinate axes:

```text
K_J(s,0)=K_J(0,t)=I.                                  (AQ.12)
```

Consequently its two first derivatives vanish at the origin.  Differentiate
the crossing in `(AQ.5)` once in each parameter:

```text
partial_(s,t)(K_J-I)|_(0,0)
 =J W(I-J)H J.                                        (AQ.13)
```

The Fredholm logarithmic derivative therefore is

```text
partial_(s,t) log c_J(s,t)|_(0,0)
 =Tr(J W(I-J)H J)
 =S_J(W,H).                                           (AQ.14)
```

This is exactly Proof 277's Toeplitz covariance and one half of its extended
Dirichlet pairing.  No finite-dimensional Jacobi theorem is needed for
`(AQ.10)--(AQ.14)`.

## 5. Relative E/R determinant line

For the nested source pair `R<=E`, define

```text
c_(E/R)(s,t)=c_E(s,t)/c_R(s,t).                       (AQ.15)
```

Both determinants in `(AQ.15)` are genuine under `(AQ.7)`.  Their quotient is
one relative determinant-line scalar; its factors must not be estimated
separately.  Equation `(AQ.14)` gives

```text
partial_(s,t) log c_(E/R)(s,t)|_(0,0)
 =S_E(W,H)-S_R(W,H).                                  (AQ.16)
```

By Proofs 253, 262, 266, 277, and 278, `(AQ.16)` is the same signed scalar as
the completed outer-minus-Sonin Dirichlet response and the recombined
outer/second-support/prolate physical branches.

Thus the continuous determinant domain needed to own this mixed covariance is
closed for each fixed finite `S`.  Its constants are not uniform in `S`, and
`(AQ.16)` is not yet the Gate 3U estimate.

## 6. Burnol multiplicative cross-ratio

This section first works in finite dimension.  Let `Q_(Jc)` be an isometry
onto `Ran(I-J)` and set

```text
d_J(X)=det(Q_(Jc)* X^(-1) Q_(Jc)).                   (AQ.17)
```

Jacobi's complementary-minor identity gives

```text
det(T_J(X))=det(X)d_J(X).                             (AQ.18)
```

Apply `(AQ.18)` to `U_sV_t`, `U_s`, and `V_t`.  The ambient determinants
cancel multiplicatively:

```text
c_J(s,t)
 =d_J(U_sV_t)/[d_J(U_s)d_J(V_t)].                    (AQ.19)
```

Equation `(AQ.19)` is a multiplicative second difference.  It cancels all
pure-`s`, pure-`t`, and ambient determinant terms before differentiation.

For the source pair, let

```text
rho(X)=d_E(X)/d_R(X).                                 (AQ.20)
```

Then

```text
c_(E/R)(s,t)
 =rho(U_sV_t)/[rho(U_s)rho(V_t)].                    (AQ.21)
```

Proof 278 identifies `rho(X)` with the one-copy outer boundary divided by the
two-copy Burnol boundary.  Proof 279 factorizes the latter, in finite
dimension, into its two diagonal channels and Schur factor.  Hence `(AQ.21)`
has the exact finite coordinate

```text
second multiplicative difference of

 det(J*X^(-1)J)
 ---------------------------------- .                (AQ.22)
 det(D_+(X))det(D_-(X))det(Omega_X)
```

In infinite dimension, `(AQ.15)` defines the determinant line.  Equations
`(AQ.21)--(AQ.22)` identify its Burnol boundary coordinate; they do not define
the four determinants in `(AQ.22)` separately.  This is the required legal
replacement for an ambient BOGC determinant at the domain level.

## 7. Zero-prolate guard

Reuse Proof 279's deterministic model:

```text
F=[[0,1,0],
   [1,0,0],
   [0,0,1]],

P_0=e_1e_1*,
v=(e_2+e_3)/sqrt(2),
W=H=vv*.                                              (AQ.23)
```

It has

```text
F_0=0,
K_prol=0,
S_E=0,
S_R=1/4,
partial_(s,t)log c_(E/R)|_0=-1/4.                    (AQ.24)
```

At the nonzero default parameters the relative cocycle log has magnitude
`0.004395863`.  The interior Toeplitz cocycle, Burnol boundary cross-ratio,
and Proof 279 channel-Schur cross-ratio agree to `5.83e-16`; the centered
finite-difference derivative agrees with `-1/4` to `2.05e-8`.

The guard proves two points.  The cocycle does not erase the genuine
two-boundary response, and its determinant domain does not depend on a
prolate-only mechanism.

## 8. What this does and does not buy

Proof 280 closes a previously open ownership question:

```text
fixed-S continuous determinant domain for S_E-S_R: closed.       (AQ.25)
```

It also gives a better starting point for the uniform estimate.  The compact
root is inserted in `U_s` before trace-class membership, and the complete
second multiplier stays inside `V_t`.  Pure one-parameter determinant history
is removed automatically by the multiplicative second difference.

The hard estimate remains

```text
|partial_(s,t) log c_(E/R)(s,t)|_(0,0)|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                    (AQ.26)
```

uniformly in the visible finite set.  The following shortcuts remain invalid:

```text
estimate c_E and c_R separately;

bound K_E-I and K_R-I by separate trace norms;

reverse the cocycle order and assume [V_t,J] in S1;

split the complete second multiplier into absolute prime words;

define the boundary factors in (AQ.22) separately;

infer a uniform bound from fixed-S Fredholm legality.             (AQ.27)
```

The next analytic move should compare the two completed crossings in
`c_(E/R)` before a norm, insert the real-line `2B_root` displacement clip, and
only then expose the causal prime law or Proof 279's boundary channels.

## 9. Literature boundary

Primary references:

```text
Burnol, explicit Sonin projection and Fourier plus/minus channels:
https://arxiv.org/abs/math/0208121

Migler, Joint torsion equals the determinant invariant:
https://arxiv.org/abs/1403.4882

Migler, Functional calculus and joint torsion of pairs of almost commuting
operators:
https://arxiv.org/abs/1409.6289
```

Migler treats determinant invariants and functional calculus for almost
commuting Fredholm operators under trace-class commutator hypotheses.  That
literature confirms the architecture, but Proof 280 does not import its
K-theoretic conclusions.  Equations `(AQ.5)--(AQ.14)` are the direct asymmetric
operator proof required here and use only the route-owned detector commutator.

## 10. Reproduction

Run in WSL2:

```text
python3 -B docs/proofs/280_toeplitz_semicommutator_cocycle_probe.py

python3 -B docs/proofs/280_toeplitz_semicommutator_cocycle_probe.py \
  --size 34 --support-rank 8 --seed 2280
```

The default cohort reports

```text
maximum algebra error                 1.27e-14,
maximum mixed-derivative error        8.94e-8,
maximum zero-prolate guard error      2.05e-8.
```

The alternate cohort reports maximum algebra error `2.05e-14` and maximum
mixed-derivative error `9.85e-8`.  The derivative uses a centered finite
difference; the crossing, Jacobi, boundary, and channel identities are direct
matrix equalities.

## 11. Route judgment

Proof 280 replaces the proposed continuous raw boundary determinant by a
genuine two-parameter semicommutator Fredholm cocycle.  It preserves the full
Proof 279 channel structure while requiring trace-class smoothing only on the
compact-root detector leg.

The active bottom is now

```text
relative completed crossings K_E-I and K_R-I
  -> same-object E/R cancellation before a trace norm
  -> compact displacement stopping on the relative path
  -> keep the complete fixed-S second multiplier whole
  -> one signed scalar derivative
  -> uniform polynomial-support bound
  -> Gate 3U.                                             (AQ.28)
```

The uniform estimate, complete prime stopping/telescope, finite-S sign,
arithmetic same-object trace identity, negative-owner integration, Burnol's
all-zero identity, and RH remain open.  No Lean owner or route consumer is
changed.

Successor note: Proof 281 shows that the relative cocycle `c_(E/R)` has an
ordinary Fredholm determinant coordinate on the common band `B=E-R`.  Its
mixed derivative is

```text
Tr(B W(I-E)H B)-Tr(R W B H R),
```

after the common `R-(I-E)` crossing cancels.  The fixed-`S` band domain is
therefore closed; the uniform signed estimate remains open.
