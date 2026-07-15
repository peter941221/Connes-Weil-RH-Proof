# Proof 262: Endpoint two-commutator Gate 3U

Date: 2026-07-15

Status: reduces Gate 3U to one endpoint pairing with two fixed source
commutators.  Proof 261 makes the ordinary trace legal, so the synchronized
time integral can be evaluated at the endpoint.  The complete Euler generator,
the path parameter, and the outer transport then disappear from the formula.

The surviving expression pairs the same dual coframe with an outer-half-line
detector crossing minus a Sonin detector crossing.  All detector dependence is
source-local and carries the compact-root support.  All finite-`S` dependence
is confined to one coframe and one Sonin graph.  This is narrower than Proof
255's intrinsic defect and Proof 253's time-dependent `D_E-D_R` form.

An exact direct-sum guard shows that metric order, a Markov inverse, detector
annihilation of the fixed mode, Q-invariance, and super-exponential prolate
decay do not imply a uniform bound.  The actual real-line compact-support
half-line geometry must enter before any Markov expansion or norm.  Gate 3U,
the arithmetic same-object identity, negative-owner integration, the Burnol
identity, and RH remain open.  No Lean owner or route rewire is authorized.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| fixed-S ordinary trace                         | legal by Proof 261           |
| synchronized time integral                     | replaced by endpoint         |
| single-projection endpoint trace formula       | exact                        |
| nested dual-frame endpoint formula             | exact                        |
| two-source-commutator collapse                 | exact                        |
| detector compact-support localization          | explicit                     |
| abstract Markov/prolate uniform theorem        | rejected by exact guard      |
| source-specific uniform endpoint estimate      | open, active Gate 3U         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The new owner is

```text
Tr(W(B_(S,1)-B_0))

 =Tr_B(mathcalD_S*
   [C_0[W,E]B-[W,R]R L_S]),                          (Y.1)
```

where

```text
C_0=I-E,
L_S=(R H_S R)^(-1)R H_S B,
mathcalD_S=the dual coframe from Proof 255.           (Y.2)
```

The bracket in `(Y.1)` must remain a difference until the real-line compact
support has removed the irrelevant translation paths.

## 2. One projection at the endpoint

Let `J` be an orthogonal projection, `T` a bounded invertible normal
convolution operator, and

```text
H=T* T,
A_J=J H J+(I-J),
D_J=A_J^(-1),
J_T=T J D_J J T*.                                    (Y.3)
```

Let `W=C_g* C_g` be the self-adjoint detector.  It commutes with `T` and `H`.
Proof 261 shows that the root-sandwiched difference is trace class, so ordinary
cyclicity applies.  Define

```text
q_J(W,H)=Tr(W(J_T-J)).                                (Y.4)
```

Cycling the first term in `(Y.4)` onto `Ran(J)` gives

```text
q_J(W,H)
 =Tr(J W H J D_J-J W J).                             (Y.5)
```

Insert `I=J+(I-J)` between `W` and `H`.  The `J H J D_J=J` term cancels the
second term in `(Y.5)`, leaving

```text
q_J(W,H)
 =Tr([J,W](I-J)H J D_J).                             (Y.6)
```

Equation `(Y.6)` replaces the time-dependent generator by the fixed source
commutator `[J,W]` and the complete endpoint metric graph.  It does not give a
uniform estimate: the graph

```text
(I-J)H J D_J                                         (Y.7)
```

can grow with the condition of `H`.

For the nested band `B=E-R`, subtraction gives

```text
Tr(W(B_T-B))=q_E(W,H)-q_R(W,H).                       (Y.8)
```

Estimating the two terms in `(Y.8)` separately repeats the rejected
half-line/Sonin triangle inequality.

## 3. Nested Schur frame and coframe

Use the orthogonal decomposition

```text
E=R direct-sum B,
C_0=I-E.                                              (Y.9)
```

Define the Sonin graph and its source frame

```text
L=(R H R)^(-1)R H B,
Z=B-RL.                                               (Y.10)
```

The frame `T Z` spans the transported band.  Its Gram operator is the Schur
complement

```text
Sigma=Z* H Z.                                         (Y.11)
```

Hence

```text
B_T=T Z Sigma^(-1)Z* T*.                             (Y.12)
```

Proof 255's dual coframe is

```text
mathcalD=H Z Sigma^(-1).                              (Y.13)
```

The inverse-metric shorting formula gives the same operator:

```text
M=H^(-1),

mathcalD
 =B-C_0(C_0 M C_0)^(-1)C_0 M B.                     (Y.14)
```

The Schur orthogonality relations are

```text
mathcalD* Z=B,
mathcalD* R=0,
mathcalD* B=B.                                       (Y.15)
```

For `W_B=B W B`, put

```text
K_0=W Z-Z W_B.                                       (Y.16)
```

Using `(Y.11)--(Y.13)` and `[W,H]=0`, the endpoint response becomes

```text
Tr(W(B_T-B))=Tr_B(mathcalD* K_0).                    (Y.17)
```

This recovers Proof 255's intrinsic formula after Proof 261 supplies its
ordinary trace legality.

## 4. Collapse to two source commutators

Expand `(Y.16)` with `Z=B-RL`:

```text
K_0
 =(I-B)W B
  -(I-R)W R L
  +R(LW_B-R W R L).                                  (Y.18)
```

The last term vanishes after multiplication by `mathcalD*` because
`mathcalD*R=0`.  Since `I-B=R+C_0` and `mathcalD*R=0`, the first term reduces
to `mathcalD*C_0 W B`.  The projection relations give

```text
C_0 W B=C_0[W,E]B,

mathcalD*(I-R)W R L
 =mathcalD*[W,R]R L.                                 (Y.19)
```

Substituting `(Y.19)` into `(Y.17)` proves `(Y.1)`:

```text
Tr(W(B_T-B))
 =Tr_B(mathcalD*
   (C_0[W,E]B-[W,R]R L)).                            (Y.20)
```

Equation `(Y.20)` contains no Euler generator, path integral, Kato unitary, or
outer transport.  The complete finite-`S` product remains inside the paired
operators `mathcalD` and `L`.

Do not estimate the two terms in `(Y.20)` separately.  The Markov/prolate guard
in Section 6 shows that either term can retain a growing conditioned response.

## 5. Compact-root support is now explicit

Let `g` be supported in `[-B_root,B_root]` and put

```text
W=C_g* C_g=C_F,
supp(F) subset [-2B_root,2B_root].                   (Y.21)
```

For the outer half-line `E`, the commutator kernel is

```text
[W,E](x,y)
 =(1_E(y)-1_E(x))F(x-y).                             (Y.22)
```

It vanishes unless

```text
|x-y|<=2B_root
```

and `x,y` lie on opposite sides of the outer boundary.

The Sonin commutator has the exact source decomposition

```text
R=E E_hat E-K_prol,

[W,R]
 =[W,E]E_hat E
   +E[W,E_hat]E
   +E E_hat[W,E]
   -[W,K_prol],                                      (Y.23)

[W,E_hat]
 =-mathcalS*[W,E]mathcalS.                           (Y.24)
```

Thus every detector term in `(Y.20)` is one of the following:

```text
an outer-boundary crossing supported within 2B_root;
a scattering-conjugate second-boundary crossing with the same support ledger;
a trace-class prolate commutator.                    (Y.25)
```

All dependence on the visible finite set now sits in `mathcalD_S` and `L_S`.
The next estimate must apply `(Y.21)--(Y.25)` before expanding either operator
through the Markov law.

## 6. Exact Markov/prolate guard

The following block family rejects an abstract uniform theorem based only on
the properties accumulated through Proof 261.

On a two-state translation space, use the Fourier basis `e_0,e_1`.  The first
vector is the Markov fixed mode.  For `0<mu<1`, define

```text
M_mu=diag(1,mu),
H_mu=M_mu^(-1),
T_mu=H_mu^(1/2),                                     (Y.26)

W_mu=Q_mu=|e_1><e_1|,

v_mu=sqrt(1-mu)e_0+sqrt(mu)e_1,
E_mu=|v_mu><v_mu|,
R_mu=0.                                               (Y.27)
```

In the physical two-point basis, with `tau` the swap translation,

```text
M_mu
 =[(1+mu)/2]I+[(1-mu)/2]tau.                         (Y.28)
```

Thus `M_mu` is a probability average of translations and `H_mu>=I`.  The
second support is invariant under `T_mu`, the detector commutes with the
transport, and

```text
W_mu e_0=0,
E_mu Q_mu E_mu=mu E_mu.                              (Y.29)
```

The last identity makes `mu` the base prolate eigenvalue.  Also
`Ran(E_mu) intersection Ran(Q_mu)={0}=Ran(R_mu)`.

The transported line is spanned by

```text
T_mu v_mu=sqrt(1-mu)e_0+e_1.                         (Y.30)
```

Its exact detector response and source commutator mass are

```text
q_mu
 =Tr(W_mu((E_mu)_(T_mu)-E_mu))
 =1/(2-mu)-mu,                                       (Y.31)

norm([W_mu,E_mu])_1
 =2sqrt(mu(1-mu)).                                   (Y.32)
```

Choose

```text
mu_n=2^(-4n^2).                                      (Y.33)
```

Then the prolate singular values `sqrt(mu_n)=2^(-2n^2)` decay faster than any
exponential, while

```text
sum_n mu_n<infinity,
sum_n norm([W_n,E_n])_1<infinity,
q_(mu_n)->1/2.                                       (Y.34)
```

For the first `N` orthogonal blocks,

```text
sum_(n<=N) q_(mu_n)=N/2+O(1).                        (Y.35)
```

The family satisfies metric order, Markov averaging, fixed-mode annihilation,
Q-invariance, nesting, and super-exponential prolate decay.  Its endpoint
response has no uniform bound as `N` grows.

This guard is not a counterexample to the CCM24/CC20 source.  It uses a direct
sum of two-point translation spaces instead of one real logarithmic half-line,
and its detector has no real-line compact-support restriction.  It proves that
Gate 3U must use `(Y.21)--(Y.25)` as source geometry.  The abstract assumptions
alone cannot close the gate.

## 7. Determinant literature does not supply the bound

In finite dimensions, `(Y.8)` can be written as the derivative of a logarithm
of the Schur-complement determinant under the perturbation `H ->exp(sW)H`.
This language preserves the nested subtraction.

The standard determinant results audited here cover different contracts:

```text
Deift--Its--Krasovsky
Toeplitz matrices and Toeplitz determinants
https://arxiv.org/abs/1207.4990

  surveys single Hardy/Toeplitz compressions and strong Szego asymptotics;

Migler
Joint torsion equals the determinant invariant
https://arxiv.org/abs/1403.4882

  treats determinant invariants for almost commuting Fredholm operators.
```

Neither source constructs the relative Fredholm determinant of the nested
CC20 Sonin Schur complement or proves a bound independent of the finite Euler
symbol.  Invoking a Toeplitz determinant name would leave the same missing
estimate and would add an unproved determinant-domain premise.

CC20 and CCM24 also contain no theorem estimating `(Y.20)` uniformly in `S`.

## 8. Corrected Gate 3U contract

For the actual compact root and synchronized finite-`S` metric, prove

```text
abs Tr_B(mathcalD_S*
  (C_0[W_g,E]B-[W_g,R]R L_S))

 <=C (1+B_root)^d norm(g)_(H^r)^2,                  (Y.36)
```

where `C,d,r` do not depend on `S`.

The proof must keep these operations in order:

```text
1. insert the CC20 decomposition (Y.23);
2. use the support restriction |x-y|<=2B_root;
3. retain the outer-minus-Sonin bracket in (Y.36);
4. expand the paired coframe/graph through a common Markov path law;
5. sum conditional probability mass rather than prime coefficients.       (Y.37)
```

The endpoint formula removes the synchronized time integral from this gate.
It also removes the need to estimate `h_(S,t)`, `B_t'`, or a Kato path length.

A proof of `(Y.36)` closes Gate 3U.  A source-realized family with bounded root
support and unbounded left side rejects the detector-specific route.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/262_endpoint_two_commutator_gate_probe.py
```

The endpoint algebra reports

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| single-projection relative trace     | 2.24e-14  |
| band subtraction                     | 7.48e-15  |
| coframe shorting identity            | 4.18e-16  |
| intrinsic endpoint identity          | 2.66e-13  |
| two-commutator endpoint identity     | 2.82e-13  |
+--------------------------------------+-----------+
```

The eight-block guard reports

```text
+-------+-------------+-------------+-------------+
| modes | response    | comm S1     | prolate S1  |
+-------+-------------+-------------+-------------+
|     1 | 0.453629    | 0.484123    | 0.0625000   |
|     2 | 0.953618    | 0.491935    | 0.0625153   |
|     4 | 1.95362     | 0.491943    | 0.0625153   |
|     8 | 3.95362     | 0.491943    | 0.0625153   |
+-------+-------------+-------------+-------------+
```

The maximum guard algebra error is `2.22e-16`; the maximum endpoint relative
error is `2.82e-13`.

Finite matrices certify the endpoint, Schur, coframe, and guard identities.
They do not prove or disprove the real-line compact-support estimate `(Y.36)`.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Gate 3L fixed-S trace legality                 | closed by Proof 261          |
| time-integrated D_E-D_R owner                  | replaced by endpoint         |
| single-projection endpoint commutator          | exact                        |
| nested Schur/coframe endpoint                  | exact                        |
| two-source-commutator formula                  | exact, active owner          |
| root-support crossing geometry                 | explicit                     |
| metric order / Markov / prolate abstraction    | insufficient by exact guard  |
| Toeplitz determinant shortcut                  | no matching source theorem   |
| uniform source endpoint bound (Y.36)           | open, Gate 3U                |
| arithmetic same-object finite-S identity       | open                         |
| negative-owner integrated smallness            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 262 removes time propagation from Gate 3U and rejects every proof based
only on abstract Markov concentration, metric order, detector fixed-mode
vanishing, or prolate decay.  The active theorem is the real-line
compact-support estimate `(Y.36)` for the paired dual coframe and Sonin graph.
