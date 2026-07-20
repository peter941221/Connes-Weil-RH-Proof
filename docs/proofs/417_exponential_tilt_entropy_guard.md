# Proof 417: Exponential-tilt endpoint guard and entropy replacement

Date: 2026-07-19

Status: exact finite-dimensional rejection of the proposed fixed-endpoint
commutator inequality, followed by a condition-number-free tilted-path
inequality.  The replacement reduces the finite response to a detector
variance and one positive compression entropy.  In the continuous Burnol
route the unsmoothed prime-log entropy is not a legal Fredholm determinant, so
a detector-localized completed entropy theorem is still required.

This proof does not close Gate 3U, prove the finite-`S` sign, prove Burnol's
identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| fixed-endpoint product inequality `(*)`              | false exactly        |
| arbitrary-projection endpoint estimate               | needs spectral cost  |
| exponential tilted-path covariance identity          | exact                |
| path response controlled by positive entropy         | exact, finite rank   |
| detector variance along Burnol endpoint path          | Proofs 375--377      |
| canonical diagonal Euler energy                       | Proof 416 polynomial |
| raw continuous atomic Euler entropy                   | not Fredholm-legal   |
| localized completed entropy-to-energy theorem         | open                 |
| Gate 3U / RH                                          | open / unproved      |
+------------------------------------------------------+----------------------+
```

The proposed shortcut was

```text
abs D Phi_P(A)[W]
 <=C norm([A,P])_2 norm([W,P])_2.                     (ET.1)
```

There is no universal constant `C` in `(ET.1)`, even for commuting diagonal
self-adjoint `A,W` and a rank-one projection `P` on `C^2`.

The correct finite-rank statement follows the whole exponentially tilted
projection path `P_t`:

```text
abs D Phi_P(A)[W]
 <=sqrt(sup_(0<=t<=1) Var_(P_t)(W))
      sqrt(Phi_P(2A)).                                (ET.2)
```

Equation `(ET.2)` has no Gram condition number.  It also explains why Proof
416's Bernstein--Szego family is not an obstruction to an energy bound: its
response is linear in `M`, while its logarithmic energy is quadratic in `M`.

The route obstruction is now precise.  For continuous prime-log translations,
the naked scalar `Phi_P(2A)` in `(ET.2)` is not defined in the trace/Fredholm
class required by the route.  Root completion makes the detector derivative
legal, but does not make the background atomic entropy legal.  The successor
must construct a positive detector-localized completion of `(ET.2)`, or prove
Proof 416 `(EN.7)` directly on Proof 415's completed boundary form.

## 2. Finite compression owner

Let `H` be finite dimensional, let `P` be an orthogonal projection, and let
`A,W` be commuting self-adjoint operators.  On `P H`, put

```text
G_t=P exp(tA)P,

P_t=exp(tA/2)P G_t^(-1)P exp(tA/2).                  (ET.3)
```

`G_t` is positive invertible and `P_t` is the orthogonal projection onto

```text
exp(tA/2) Ran(P).                                     (ET.4)
```

Define the compression Jensen gap

```text
Phi_P(A)
 =log det(P exp(A)P|_(P H))-Tr(PAP).                 (ET.5)
```

Differentiating in a commuting direction `W` gives

```text
D Phi_P(A)[W]
 =Tr[G_1^(-1)P W exp(A)P]-Tr(PWP)
 =Tr[W(P_1-P)].                                      (ET.6)
```

Thus `(ET.6)` is exactly the Gram-corrected transported projection response,
not a surrogate determinant statistic.

Inserting `I=P+(I-P)` between the two commuting multipliers also gives the
fixed-endpoint boundary form

```text
D Phi_P(A)[W]
 =Tr[G_1^(-1)P exp(A)(I-P)WP].                       (ET.7)
```

Equation `(ET.7)` is the finite-rank version of Proof 415 `(CB.3)`.  It makes
the failure mechanism in the next section transparent: `G_1^(-1)` can amplify
the crossing before the trace is taken.

## 3. Exact rank-one counterexample

For `M>0`, set

```text
epsilon=exp(-M),
A_M=diag(0,M),
W=diag(0,1),

p_M=(sqrt(1-epsilon),sqrt(epsilon)),
P_M=|p_M><p_M|.                                      (ET.8)
```

The operators `A_M` and `W` commute.  The tilted vector at `t=1` is

```text
exp(A_M/2)p_M
 =(sqrt(1-epsilon),1),                               (ET.9)
```

so `(ET.6)` is the exact scalar

```text
R_M
 :=D Phi_(P_M)(A_M)[W]
 =1/(2-epsilon)-epsilon
 ->1/2.                                              (ET.10)
```

For a diagonal operator `D=diag(d_0,d_1)` and this rank-one projection,

```text
norm([D,P_M])_2^2
 =2 abs(d_1-d_0)^2 epsilon(1-epsilon).                (ET.11)
```

Consequently,

```text
norm([A_M,P_M])_2 norm([W,P_M])_2
 =2M epsilon(1-epsilon)
 ->0.                                                (ET.12)
```

Combining `(ET.10)--(ET.12)`, the constant required in `(ET.1)` obeys

```text
C_M>=R_M/[2M epsilon(1-epsilon)]
    ~exp(M)/(4M).                                     (ET.13)
```

This is an analytic counterexample.  No numerical limit or ill-conditioned
linear solve is used.

There is a general but route-useless repair.  If the spectrum of `A` lies in
`[a_-,a_+]`, then `(ET.7)`, the lower bound

```text
G_1>=exp(a_-)P,                                      (ET.14)
```

and Duhamel's formula

```text
[exp(A),P]
 =integral_0^1 exp((1-s)A)[A,P]exp(sA) ds             (ET.15)
```

give

```text
abs D Phi_P(A)[W]
 <=exp(a_+-a_-)/sqrt(2)
      norm([A,P])_2 norm([W,P])_2.                   (ET.16)
```

The exponential spectral-oscillation factor in `(ET.16)` is not an artifact:
`(ET.13)` shows that a universal endpoint estimate needs exponential growth up
to a polynomial factor.  Such a factor would destroy the canonical polynomial
support budget, so `(ET.16)` cannot be the Gate 3U estimate.

## 4. Follow the tilted projection path

Let

```text
F(t)=log det G_t.                                    (ET.17)
```

Rectangular trace cycling gives

```text
F'(t)=Tr(A P_t).                                     (ET.18)
```

The derivative of the range projection in `(ET.3)` is

```text
P_t'
 =1/2 (I-P_t)A P_t+1/2 P_t A(I-P_t).                (ET.19)
```

For any self-adjoint multiplier `X`, define its projection variance

```text
Var_(P_t)(X)
 :=Tr[P_t X(I-P_t)X P_t]
 =1/2 norm([X,P_t])_2^2.                             (ET.20)
```

Because `A` and `W` commute, `(ET.19)` gives the exact mixed covariance

```text
d/dt Tr(WP_t)
 =Tr[P_t A(I-P_t)W P_t].                             (ET.21)
```

The right side is real: after expanding `I-P_t`, the two possible orders differ
only by a finite trace cycle on `P_t H`.

Hilbert--Schmidt Cauchy--Schwarz now yields

```text
abs d/dt Tr(WP_t)
 <=sqrt(Var_(P_t)(A)) sqrt(Var_(P_t)(W)).             (ET.22)
```

Define the symmetric tilt energy

```text
J_P(A)
 :=Tr[A(P_1-P)]
 =integral_0^1 Var_(P_t)(A) dt.                      (ET.23)
```

Integrating `(ET.22)` and applying Cauchy--Schwarz in `t` gives

```text
abs D Phi_P(A)[W]
 <=sqrt(sup_t Var_(P_t)(W)) sqrt(J_P(A)).             (ET.24)
```

Finally set

```text
phi(t)=Phi_P(tA)=F(t)-tF'(0).                        (ET.25)
```

The Gram determinant is a log-Laplace transform, so `phi` is convex,
`phi(0)=phi'(0)=0`, and `phi(t)>=0`.  Hence

```text
J_P(A)=phi'(1)
 <=phi(2)-phi(1)
 <=Phi_P(2A).                                        (ET.26)
```

Equations `(ET.24)--(ET.26)` prove `(ET.2)`.

This is the correct finite-dimensional replacement for `(ET.1)`:

```text
fixed endpoint commutators       -> false;
whole tilted detector variance   -> condition-number-free;
positive compression entropy     -> pays for Gram amplification. (ET.27)
```

## 5. Relation to the canonical Burnol family

Write the finite Euler multiplier as

```text
tau_S=exp(L_S),
A_S=log(abs(tau_S)^2)=L_S+conj(L_S).                 (ET.28)
```

Every factor of `tau_S` is zero-free and boundedly invertible in the causal
Hardy half-plane, so `tau_S^t=exp(tL_S)` is a legal analytic multiplier for
`0<=t<=1`.  Proof 375's argument therefore makes every range

```text
M_t=tau_S^t M_0                                      (ET.29)
```

nearly invariant.

Let `u_t=tau_S^t/abs(tau_S)^t` be the boundary phase.  Multiplication by `u_t`
is unitary and commutes with every detector multiplier `W`.  The positive
tilt range in `(ET.3)` and the analytic range `(ET.29)` satisfy

```text
M_t=u_t exp(tA_S/2)M_0.                              (ET.30)
```

Thus the detector variances are identical in the two coordinates.  Proofs
376--377 give, for compact roots, a polynomial support/Sobolev bound for

```text
sup_(0<=t<=1) Var_(P_(M_t))(W).                      (ET.31)
```

This is exactly the first factor of `(ET.2)`.  Proof 416 gives the canonical
diagonal Euler budget

```text
E(S_F)
 =sum_(p in S_F)sum_(m>=1) log(p)/(m p^m)
 <=C(1+B_F)^2.                                       (ET.32)
```

The remaining desired arrow is therefore scalar:

```text
canonical Euler energy `(ET.32)`
  ->positive completed compression entropy
  ->boundary response through `(ET.2)`.              (ET.33)
```

This is narrower than trying to estimate the detector gradient directly.  It
also keeps the mixed Fredholm remainder from Proof 415: that remainder is part
of the positive entropy rather than being deleted frequency by frequency.

## 6. Continuous trace-legality guard

Equation `(ET.2)` is not yet a Gate theorem.  On the real Mellin line, a
prime-log mode

```text
exp(i ell s)                                         (ET.34)
```

is translation by `ell` in the physical logarithmic coordinate.  Its
commutator with a sharp half-line projection restricts a translation to an
interval of length `abs(ell)`.  That restriction has infinite rank and is not
Hilbert--Schmidt.  Therefore the raw atomic background does not define the
naked Fredholm determinant `Phi_P(2A_S)` in `(ET.2)`.

Proof 261 proves something deliberately weaker and legal:

```text
compact-root-sandwiched detector derivative is trace class. (ET.35)
```

It does not prove that the detector-free Euler entropy is finite.  Forming
four bare weighted determinants, applying `(ET.2)`, and subtracting infinities
afterward would violate Proofs 261, 343, 406, and 407.

A valid successor must construct a positive localized completion with both
properties

```text
abs Lambda_(S_F)(F)^2
 <=C_root(B_F,F) mathfrakE_(S_F,F),                  (ET.36)

mathfrakE_(S_F,F)
 <=C_lambda P(B_F) E(S_F),                           (ET.37)
```

where `Lambda` is Proof 415's single completed weighted boundary form.  The
construction must reproduce Proof 405's combined prolate/reflected-support
corner and Proof 264's trace anomaly.  The symbol `mathfrakE` in
`(ET.36)--(ET.37)` is a theorem contract, not an already constructed
determinant.

Equivalently, one may bypass `mathfrakE` and prove Proof 416 `(EN.7)` directly.
What is no longer viable is the fixed-endpoint product `(ET.1)`.

## 7. Consistency with the Proof 416 guard

For Proof 416's outer multiplier

```text
m_(M,r)(z)=(1-rz)^(-M),
A=log(abs(m_(M,r))^2),                               (ET.38)
```

the positive Fourier coefficients are

```text
A_n=M r^n/n,  n>=1.                                  (ET.39)
```

Hence its scalar strong-Szego energy is

```text
sum_(n>=1)n abs(A_n)^2
 =M^2 sum_(n>=1)r^(2n)/n
 =-M^2 log(1-r^2).                                   (ET.40)
```

The response `2Mr` from Proof 416 is therefore fully compatible with an
energy-to-boundary theorem: the energy grows like `M^2`.  The example rejects
finite defect alone, not `(ET.33)`.

## 8. Source audit

Bottcher's positive model-space BOGC formula proves the finite-Blaschke
strong-Szego upper bound used in Proof 346:

```text
Albrecht Bottcher,
Borodin-Okounkov and Szego for Toeplitz operators on model spaces,
Theorem 1.1,
https://arxiv.org/abs/1307.0329
```

Laptev--Safarov study trace errors between functional calculus and
compressions, but their finite-rank/spectral-projection hypotheses do not turn
the non-Hilbert--Schmidt atomic crossing in `(ET.34)` into the completed
root-relative determinant required here:

```text
A. Laptev and Yu. Safarov,
Szego Type Limit Theorems,
Journal of Functional Analysis 138 (1996),
https://doi.org/10.1006/jfan.1996.0075
author copy: https://www.ma.ic.ac.uk/~alaptev/Papers/sz.pdf
```

Burnol's projection and de Branges identification remain the source of the
actual carrier:

```text
Jean-Francois Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation de Fourier,
Theorems 4 and 8,
https://arxiv.org/abs/math/0208121
```

None of these sources states `(ET.36)--(ET.37)` for the weighted Burnol carrier
and atomic prime-log background.

## 9. Reproducible certificate

The companion script evaluates `(ET.8)--(ET.13)`, integrates the covariance in
`(ET.21)`, and checks the entropy majorant `(ET.26)`:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/417_exponential_tilt_entropy_guard_probe.py
```

The numerical integration certifies the displayed finite algebra only.  The
counterexample is the exact formula `(ET.10)--(ET.13)`.

## 10. Decision

```text
fixed-endpoint inequality `(*)`:              rejected analytically;
endpoint bound with `exp(osc(A))`:            valid but route-useless;
tilted-path covariance identity:              exact;
finite entropy replacement `(ET.2)`:          exact;
Burnol path detector variance:                already controlled;
canonical Euler diagonal energy:              polynomial by Proof 416;
localized completed entropy `(ET.36)`:        open active producer;
Gate 3U / finite-S sign / Burnol / RH:         open / open / open / unproved.
```
