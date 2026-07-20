# Proof 415: Canonical-family quantifier cut and mixed boundary survivor

Date: 2026-07-19

Status: analytic, with no numerical experiment.  An exact finite-model
calculation proves that a localized weighted determinant retains a mixed
high-frequency boundary term even when its diagonal localized Szego ledger is
zero.  General BOGC or compressed-shift algebra therefore cannot prove Proof
414 `(WS.29)` by deleting all near off-diagonal pairs.

The route quantifier is also narrowed.  After an exact-support bridge, the RH
consumer can use the visible-prime family derived from the selected test's
nonzero prime-power terms.  A bound uniform over every unrelated finite prime
set is sufficient but stronger than the route needs.  The corrected target is
a support-coupled canonical-family bound, or the still weaker bound along the
resonant Yoshida contradiction sequence.

This proof does not establish either corrected bound.  Gate 3U in its current
universal form, the canonical-family replacement, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| generic determinant deletes all near-frequency pairs | false analytically   |
| exact mixed boundary response on `K_(z^N)`           | positive, order `ab` |
| localized diagonal ledger controls that response     | false without a      |
|                                                      | boundary remainder   |
| arbitrary finite-`S` supremum needed by RH consumer  | no                   |
| selected-test canonical family sufficient for route  | yes                  |
| exact-support-to-family Lean bridge                  | open                 |
| canonical-family Burnol boundary estimate            | open                 |
| direct RH bypass supplied here                       | no                   |
| RH                                                   | unproved             |
+------------------------------------------------------+----------------------+
```

The exact obstruction has the form

```text
two high shifts `k` and `k+1`
  -> their difference lies in the detector window
  -> Gram normalization cancels the bulk
  -> one rank-two endpoint term survives.               (CF.1)
```

The last term is the finite Toeplitz analogue of the Burnol/Sonin boundary
Fredholm remainder.  A valid Gate proof must bound its complete Euler
resummation.  The scalar strong-Szego square term does not contain it.

## 2. Exact positive detector model

Work on `ell2(Z)` with bilateral shift

```text
U e_j=e_(j+1).                                         (CF.2)
```

For `N>=2`, let `P_N` project onto

```text
K_N=span{e_0,...,e_(N-1)}=K_(z^N).                    (CF.3)
```

Choose

```text
k>=N+1,
0<a,b<1,
T=(I-a U^k)(I-b U^(k+1)).                             (CF.4)
```

The four translates in `T K_N` start at

```text
0, k, k+1, 2k+1.                                      (CF.5)
```

Only the middle two translates overlap at a displacement visible to `K_N`.
Put

```text
J=P_N U P_N |_K_N,
K=J+J*,
c=(1+a^2)(1+b^2),
d=ab.                                                  (CF.6)
```

Direct multiplication of the four coefficients in `(CF.4)` gives the exact
range Gram

```text
G=P_N T* T P_N |_K_N=c I+d K.                         (CF.7)
```

No asymptotic enters `(CF.7)`.  Every other nonzero Fourier coefficient of
`T*T` has absolute displacement at least `k>=N+1`, so its `P_N` compression
vanishes.

Use the positive root detector

```text
C=I+U,
W=C* C=2I+U+U*.                                       (CF.8)
```

Its physical root has the two-point support `{0,1}`.  Let `Q_T` be the
orthogonal projection onto `T K_N`:

```text
Q_T=T P_N G^(-1)P_N T*.                               (CF.9)
```

All operators in this section have finite rank after compression, so ordinary
trace cyclicity applies.

## 3. Closed-form mixed response

The transported detector trace is

```text
Tr[W Q_T]
 =Tr_K_N[G^(-1)P_N T* W T P_N].                      (CF.10)
```

The multiplier `W` commutes with `T`.  The same support calculation used in
`(CF.7)` gives

```text
P_N T*(U+U*)T P_N
 =cK+d(J^2+(J*)^2+2I).                               (CF.11)
```

Define the sum of the two endpoint projections

```text
E_boundary
 =e_0 tensor e_0+e_(N-1) tensor e_(N-1).             (CF.12)
```

The truncated shift satisfies

```text
K^2=J^2+(J*)^2+2I-E_boundary.                         (CF.13)
```

Equations `(CF.7)`, `(CF.11)`, and `(CF.13)` yield

```text
P_N T*(U+U*)T P_N
 =K G+d E_boundary.                                  (CF.14)
```

Substitute `(CF.14)` into `(CF.10)`.  The `2I` part of `W` contributes `2N`
at both endpoints.  The `K G` term has trace `Tr(K)=0`.  Therefore

```text
Tr[W(Q_T-P_N)]
 =d Tr[G^(-1)E_boundary]
 =2d <e_0,G^(-1)e_0>.                                (CF.15)
```

Reflection symmetry gives the second equality.  Since

```text
(c-2d)I<=G<=(c+2d)I,
c-2d=1+(a-b)^2+a^2b^2>0,                             (CF.16)
```

the response obeys the explicit bounds

```text
2ab/((1+a^2)(1+b^2)+2ab)
 <=Tr[W(Q_T-P_N)]
 <=2ab/((1+a^2)(1+b^2)-2ab).                        (CF.17)
```

In particular,

```text
Tr[W(Q_T-P_N)]>0.                                    (CF.18)
```

This is a proof by finite operator algebra.  It uses no finite-difference
calculation, matrix sample, limiting fit, or unproved trace cycle.

## 4. Consequence for the localized Szego proposal

The analytic logarithm of `(CF.4)` has frequencies

```text
m k and n(k+1),  m,n>=1.                              (CF.19)
```

If the diagonal localization window is smaller than `k`, it sees no term in
`(CF.19)`.  Its localized diagonal energy is zero.  The detector `(CF.8)`
still sees the difference

```text
(k+1)-k=1,                                           (CF.20)
```

and `(CF.15)` gives a nonzero response of order `ab`.

At Euler scale,

```text
a=p^(-1/2),
b=q^(-1/2),
q/p in a fixed compact interval,                     (CF.21)
```

the survivor has size comparable to

```text
1/sqrt(pq),                                          (CF.22)
```

matching Proof 251's mixed-prime curvature scale.

Thus Proof 414 `(WS.29)` cannot mean

```text
localized determinant response
  =localized diagonal square ledger.                 (CF.23)
```

The only viable form is

```text
localized determinant response
  =diagonal square ledger
   +complete boundary Fredholm remainder,             (CF.24)

with the remainder resummed before any pairwise
absolute value.                                       (CF.25)
```

Equation `(CF.15)` proves that the remainder can contain genuine mixed
frequencies.  It does not prove that the complete Burnol remainder is
unbounded.  Gram inversion can resum many mixed pairs, so summing `(CF.17)`
over prime pairs would repeat the termwise-absolute-value error rejected by
Proofs 251, 260, and 413.

## 5. Exact full weighted boundary form identity

The finite calculation has a direct bounded-weight counterpart.  Let

```text
P=P_theta,
Q=I-P,
G_h=P M_h P|_(K_theta)=A_theta(h),                   (CB.1)
```

where `h` is a bounded positive weight and `G_h` is invertible.  Let `w` be a
bounded detector multiplier.  Since scalar multipliers commute, insert
`I=P+Q` between them:

```text
A_theta(h w)
 =P M_h(P+Q)M_wP

 =G_h A_theta(w)+P M_h Q M_wP.                       (CB.2)
```

Multiply `(CB.2)` by `G_h^(-1)` on the left.  The factors cancel in their
displayed order:

```text
G_h^(-1)A_theta(h w)-A_theta(w)
 =G_h^(-1)P M_h Q M_wP.                              (CB.3)
```

Equation `(CB.3)` uses no determinant, asymptotic, or trace cycle.  It is the
normalized Toeplitz semicommutator for the full weight, rather than a first
variation of that weight.

Burnol's extremal multiplier need not belong to `L^infinity`.  The route must
therefore retain the form-level definition

```text
mathcalB_h(w)
 :=A_theta(h w)-G_h A_theta(w).                       (CB.3a)
```

For bounded `h`, `(CB.2)` identifies this form with
`P M_h Q M_wP`.  For the route weight, `(CB.3a)` defines the bounded extension
from the two already owned truncated Toeplitz forms.  No claim is made that
`M_h` acts boundedly on the ambient `L2` space.

Apply `(CB.3)` to

```text
h_S=abs(g_0 tau_S)^2,
h_0=abs(g_0)^2.                                      (CB.4)
```

The common `A_theta(w)` cancels before a trace is formed.  Proof 413's legal
functional becomes the completed boundary difference

```text
Lambda_S(F)
 =Tr[
    G_S^(-1)mathcalB_(h_S)(w_F)
    -G_0^(-1)mathcalB_(h_0)(w_F)].                    (CB.5)
```

In the infinite Burnol space, `(CB.5)` denotes the displayed difference as
one root-completed trace-class object.  This proof asserts neither a separate
ordinary trace for either summand nor an ambient bounded multiplier `M_(h_S)`.

The Gate problem has therefore lost one unnecessary layer:

```text
weighted relative determinant cumulants
  -> exact cancellation `(CB.2)--(CB.5)`
  -> one normalized boundary semicommutator difference. (CB.6)
```

The determinant remains a possible organizational tool, but Gate 3U no longer
needs a theorem that computes all of its cumulants.  It needs a uniform
estimate for `(CB.5)` on the support-coupled Euler family.  The finite survivor
`(CF.15)` proves that the boundary term cannot be set to zero or replaced by
the diagonal square ledger.

## 6. The route uses a canonical visible family

The concrete finite-`S` owner does not accept an independent place list after
the family has been chosen.  It derives the visible primes from that family's
prime-power terms:

```text
family.terms
  -> deduplicate the prime bases
  -> family.visiblePrimes
  -> CCM24 transport and Sonin projection.            (CF.26)
```

Repository evidence:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSProjectionTrace.lean:33-49

docs/proofs/320_finite_s_projection_trace_ledger.md
```

The arithmetic trace identity needs a set `S` containing the primes visible to
the selected test; prime-power terms outside the support cutoff vanish:

```text
docs/proofs/016_corrected_trace_identity.md:157-164
```

The current `FinitePrimePowerFamily` structure records only `terms`, primality,
and nonzero exponents.  It does not state that `terms` equals the selected
test's exact arithmetic support.  Thus the next definition is a mathematical
route specialization and a Lean bridge obligation, not an existing constructor
claimed by this proof.

For one selected compact test `F`, let

```text
family(F).terms
 =the exact nonzero prime-power atoms of F,

S_F=family(F).visiblePrimes.                          (CF.27)
```

After that exact-support bridge is supplied, the route can consume the response
for `S_F`.  Logic gives

```text
bound for every finite S
  -> bound for S_F
  -> route consumer,                                  (CF.28)
```

while the route consumer does not imply or require the first line.  Extra
primes with zero arithmetic atom alter the semilocal projection but add no
named arithmetic term.  The RH contradiction has no reason to insert them.

The current projective-root formulation

```text
sup_(finite S) ||Lambda_S||_(R_B^r)*
 <=C(1+B)^d                                           (CF.29)
```

is therefore a strong sufficient theorem.  The support-coupled theorem is

```text
|Lambda_(S_F)(F)|
 <=C(1+B_F)^d norm(F)_(R_(B_F)^r).                   (CF.30)
```

For the contradiction argument generated by one hypothetical off-line zero,
the route needs less:

```text
|Lambda_(S_(F_n))(F_n)|
 <=P(B_n) norm(g_n)_(H^r)^2                          (CF.31)
```

along Proof 249's resonant Yoshida sequence.  Its critical-line norm contracts
at an exponential rate while `B_n` grows linearly.  A polynomial `P` then
makes the residual tend to zero.

Equations `(CF.30)--(CF.31)` remove unrelated finite prime sets from the
quantifier.  They do not estimate the canonical mixed boundary remainder.

## 7. Source audit

Bottcher proves the finite-Blaschke BOGC identity used in Proofs 345--346:

```text
Albrecht Bottcher,
Borodin-Okounkov and Szego for Toeplitz operators on model spaces,
Theorem 1.1,
https://arxiv.org/abs/1307.0329
```

His formula keeps a model-space Fredholm quotient in addition to the scalar
Szego term.  Equation `(CF.15)` exhibits a mixed boundary contribution from
that quotient.

Bessonov proves triangular factorization for every positive bounded
invertible Wiener-Hopf operator on a finite interval, but his theorem supplies
no condition-number-free derivative bound for `(CF.30)`:

```text
R. V. Bessonov,
Sampling measures, Muckenhoupt Hamiltonians, and triangular factorization,
Theorem 3,
https://arxiv.org/abs/1603.07533
```

The available sources therefore justify the owner and factorization.  They do
not bound the route's canonical mixed boundary response.

## 8. Decision

```text
generic localized diagonalization:          rejected by `(CF.15)`;
full weighted owner:                        exact boundary identity `(CB.5)`;
ambient `M_(h_S)` boundedness:               not claimed;
universal all-finite-S Gate as route minimum: over-strong by `(CF.26)--(CF.28)`;
canonical-family Gate `(CF.30)`:             exact sufficient target;
Yoshida-sequence Gate `(CF.31)`:             weakest RH-facing target;
exact-support-to-family Lean bridge:          open;
Burnol/Sonin mixed-boundary estimate:        open;
direct RH bypass:                            absent;
RH:                                          unproved.
```

The next analytic calculation should prove the form-domain identification of
`(CB.5)` with Proof 405's complete reflected-support/prolate two-branch corner
and estimate that one
boundary semicommutator after the canonical Euler family has been resummed.
The target is neither a diagonal Euler norm nor a pairwise mixed-prime series.
