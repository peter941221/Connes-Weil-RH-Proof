# Proof 256: One-sided shorting collapse

Date: 2026-07-15

Status: exact elimination of the conditioned inverse left in Proof 255 and a
reproducible complementary finite-section certificate.  In the actual
one-sided Euler orientation, the inverse-metric coframe

```text
D=B-C(C M C)^(-1) C M B
```

is exactly the causal oblique lift

```text
D=T E T^(-1) B.
```

Thus `(C M C)^(-1)` is not an independent analytic target.  The complete
dual-frame response splits into one hard Sonin graph channel and one
two-crossing half-line channel.  The former remains open.  This is not a
uniform detector bound, a finite-S sign, or an RH proof.  No Lean owner or
route rewire is authorized.

## 1. Result first

```text
+------------------------------------------+----------------------------------+
| object                                   | verdict                          |
+------------------------------------------+----------------------------------+
| inverse-metric shorted coframe D         | exact                           |
| compressed inverse (C M C)^(-1)          | algebraically eliminated         |
| causal oblique lift T E T^(-1) B         | exact                           |
| hard-linear/two-crossing response split  | exact                           |
| periodic coframe collapse                | invalid model of one-sidedness   |
| zero-fill actual shorting collapse       | spoiled by outer-end nonnormality|
| continuous hard Sonin graph channel      | open, new analytic bottom        |
| uniform detector remainder bound         | open                             |
| RH                                       | unproved                         |
+------------------------------------------+----------------------------------+
```

The route move is

```text
conditioned inverse estimate
        |
        v
one-sided spectral-factor cancellation
        |
        v
causal oblique half-line lift
        |
        +-- two-crossing coframe correction
        |
        +-- complete-S Sonin graph channel.                         (O.1)
```

Only the last two branches in `(O.1)` require analysis.  The first is already
in the shape controlled by the completed-crossing machinery of Proofs
228--234.  The second is the new exact bottom.

## 2. Source orientation

Use the nested source geometry from Proofs 224--255:

```text
R <= E,
B=E-R,
C=I-E.                                                   (O.2)
```

Here `E` is the half-line orientation crossed by the finite Euler transport,
`R` is the archimedean Sonin projection, `B` is its orthogonal complement in
`E`, and `C` is the opposite half-line.

The source finite-place multiplier is the CCM24 factor

```text
T_p=I-p^(-1/2) U_(-log p).                              (O.3)
```

The exact source locations are:

```text
CCM24, https://arxiv.org/html/2310.18423v2
  mainc2m24fine.tex:946--981    finite Euler multiplier
  mainc2m24fine.tex:983--1029   Sonin transport
  mainc2m24fine.tex:1031--1073  common carrier, changed norm

CC20, https://arxiv.org/abs/2006.13771
  weil-compo.tex:1072--1103     Sonin/prolate decomposition
  weil-compo.tex:2087--2120     legal smoothed boundary commutators
```

Proof 222 fixes the translation convention.  In the cell model

```text
S e_n=e_(n-1),
E projects onto n>=0,
C projects onto n<0.                                   (O.4)
```

Therefore `C` is invariant under `S`.  It is also invariant under every
finite Euler product `T`, and under its Neumann-series inverse.

Normalize the complete finite-S transport as in Proof 253.  Scalar
normalization does not change any transported range.  Put

```text
H=T* T,
M=H^(-1),
A=T^(-1).                                              (O.5)
```

The whole-line Euler convolution is normal.  Hence `A` is normal and

```text
M=A A*=A* A.                                           (O.6)
```

Both pieces of `(O.6)` matter.  The actual inverse metric is `A A*`; normality
allows the causal factorization to use `A* A`.

## 3. Exact collapse of the conditioned inverse

Let

```text
A_C=C A C : Ran(C) -> Ran(C).                          (O.7)
```

Invariance of `Ran(C)` under `A` gives

```text
(I-C) A C=0,
C A*(I-C)=0.                                          (O.8)
```

Using the reordered metric from `(O.6)`, equations `(O.7)--(O.8)` give

```text
C M C
 =C A* A C
 =A_C* A_C,                                           (O.9)

C M B
 =C A* A B
 =A_C* C A B.                                        (O.10)
```

The restriction `A_C` is invertible because both `A` and `T=A^(-1)` preserve
`Ran(C)`.  Therefore

```text
(C M C)^(-1) C M B
 =(A_C* A_C)^(-1) A_C* C A B
 =A_C^(-1) C A B.                                    (O.11)
```

Substitution into Proof 255's coframe gives

```text
D
 =B-C A_C^(-1) C A B.                                (O.12)
```

On `Ran(C)`, `T` is `A_C^(-1)`.  Since `E=I-C` and `T A=I`,

```text
T E A B
 =T(I-C)A B
 =B-T C A B
 =B-C A_C^(-1) C A B
 =D.                                                  (O.13)
```

Thus

```text
D=T E T^(-1)B.                                       (O.14)
```

Equation `(O.14)` is the main result.  The coframe is the restriction to the
base band of the oblique projection `T E T^(-1)` onto the transported
half-line.  There is no independent conditioned-return operator left to
estimate.

This identity is a project derivation.  The operator-theory sources audited
in Proof 255 explain why Hardy angles, shorted operators, and Hankel
commutators are relevant, but they do not state `(O.14)` for this Euler/Sonin
owner or supply an `S`-uniform bound.

## 4. Exact response split

Retain Proof 255's primal Sonin graph:

```text
A_R=R H R,
L=A_R^(-1) R H B,
Z=B-R L.                                               (O.15)
```

For the legal convolution detector `W`, put

```text
W_B=B W B,
Y=W Z-Z W_B,
K_E=D-B.                                               (O.16)
```

Because `B Z=B` and `B R=0`,

```text
B Y
 =B W(B-RL)-B W B
 =-B W R L.                                           (O.17)
```

Since `D=B+K_E`, Proof 255's intrinsic response becomes

```text
D*Y
 =-B W R L+K_E*Y.                                    (O.18)
```

The two terms have different analytic roles:

```text
-B W R L
  complete-S Sonin graph channel;

K_E*Y
  causal coframe crossing paired with the intrinsic detector crossing.
                                                               (O.19)
```

By `(O.14)`,

```text
K_E=(T E T^(-1)-E)B.                                  (O.20)
```

Thus the second branch contains a genuine half-line crossing and no hidden
compressed inverse.  It should be estimated only after the scattering and
prolate branches are completed, using the trace-legality machinery already
developed in Proofs 228--234.

The first branch is not proved small by `(O.14)`.  Calling the whole problem
closed would merely rename `L`.

## 5. Why no finite matrix can model every hypothesis

The continuous proof uses two properties simultaneously:

```text
A is normal;
Ran(C) is invariant but not reducing for A.             (O.21)
```

This is natural for a bilateral convolution and a one-sided Hardy subspace.
It cannot occur nontrivially for a finite normal matrix: every invariant
subspace of a finite-dimensional normal operator is reducing.

Consequently the certificate deliberately uses two complementary models:

```text
+----------------------+---------------------+-----------------------------+
| finite model         | preserves           | necessarily loses           |
+----------------------+---------------------+-----------------------------+
| periodic FFT         | convolution normality| invariant one-sided halfline|
| causal zero-fill     | triangular halfline  | normality at outer endpoint |
+----------------------+---------------------+-----------------------------+
```

The exact block certificate separately imposes the reordered factor
`M=A* A` and causal triangularity.  This checks the algebra in
`(O.9)--(O.14)` without pretending that a finite normal matrix realizes the
continuous geometry.

## 6. Reproducible certificate

Run in the isolated WSL2 verification snapshot:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/256_one_sided_shorting_collapse_probe.py
```

The hard gates report:

```text
maximum triangular error       4.47e-16
maximum response split error   7.13e-12
certificate                    PASS
```

The exact triangular block reports:

```text
+--------------------------------+-----------+
| check                          | error     |
+--------------------------------+-----------+
| preserved half-line            | 0         |
| metric factorization           | 0         |
| cross factorization            | 0         |
| triangular coframe             | 1.91e-17  |
| oblique coframe                | 1.62e-16  |
| coframe pairing                | 0         |
+--------------------------------+-----------+
```

The periodic Sonin sections verify only `(O.18)`:

```text
+------+-------+-----------+----------+------------+----------+
| size | step  | graph norm| hard     | correction | complete |
+------+-------+-----------+----------+------------+----------+
|  192 | 0.080 | 1.8904    | +1.0831  | -2.4983    | -1.4152  |
|  208 | 0.080 | 1.8976    | +1.0015  | -2.2568    | -1.2552  |
|  288 | 0.060 | 1.9818    | +1.2431  | -2.5048    | -1.2617  |
|  320 | 0.050 | 2.0418    | +1.3291  | -2.4158    | -1.0867  |
+------+-------+-----------+----------+------------+----------+
```

Their coframe-collapse error is about `0.99`, exactly because a periodic
circle has no invariant half-line.  The split itself is at roundoff scale and
does not show the catastrophic `10^11` subtraction rejected by Proof 255.

The causal zero-fill section reports:

```text
+--------------------------------------+-----------+--------------------------+
| diagnostic                           | value     | interpretation           |
+--------------------------------------+-----------+--------------------------+
| inverse error                        | 9.70e-15  | finite causal inverse     |
| normality error                      | 1.391     | outer endpoint is real    |
| actual shorted/oblique error         | 0.965     | not a theorem failure     |
| reordered shorted/oblique error      | 1.95e-13  | normal-factor formula     |
| triangular/oblique error             | 3.32e-15  | causal identity exact     |
| full detector/transport commutator   | 0.289     | boundary pollution        |
| central commutator Frobenius norm    | 5.35e-14  | convolution locally exact |
| hard/correction response split error | 2.33e-14  | algebra exact             |
+--------------------------------------+-----------+--------------------------+
```

The nonzero direct-response discrepancy is not accepted as evidence against
`(O.14)`: finite zero-fill destroys global normality and the compact Toeplitz
detector commutes with the causal transport only away from the artificial
outer boundary.  The central commutator diagnostic confirms that mechanism.

## 7. The next original reduction

The hard branch in `(O.18)` should not be attacked by a raw norm of `L`.
Introduce the second support projection `Q` defining the Sonin intersection,
so `R<=Q`.  Then the first cross block has the exact split

```text
B W R
 =B Q W R+B(I-Q)W R.                                  (O.22)
```

When `Q R=R`, the second branch is

```text
B(I-Q)W R
 =B(I-Q)[W,Q]R.                                      (O.23)
```

It is therefore a legally smoothed second-half-line crossing.  The first
branch is the prolate leakage.  In the exact CC20 two-projection geometry,

```text
E Q E=R+K_prol,
B=E-R,                                                (O.24)
```

so

```text
(B Q)(B Q)*=B Q B=K_prol on Ran(B).                   (O.25)
```

Thus both pieces of the allegedly hard factor `B W R` begin with an existing
compact owner:

```text
B Q       -> square root of the prolate leakage;
(I-Q)[W,Q]-> completed detector crossing.             (O.26)
```

The remaining graph factor should be handled along the synchronized path,
not at the ill-conditioned endpoint.  For `0<=t<=1`, define

```text
A_t=R H_t R,
L_t=A_t^(-1)R H_t B,
Z_t=B-R L_t.                                          (O.27)
```

Differentiating `A_t L_t=R H_t B` gives the exact Riccati-free equation

```text
L_t'=A_t^(-1) R H_t' Z_t.                            (O.28)
```

If `T_t'=X_t T_t`, put

```text
K_t=X_t*+X_t,
V_(R,t)=T_t R A_t^(-1/2),
G_t=T_t Z_t.                                          (O.29)
```

Then `V_(R,t)` is an isometry, `V_(R,t)* G_t=0`, and

```text
L_t'
 =A_t^(-1/2) V_(R,t)* K_t G_t.                       (O.30)
```

Every scalar part of `K_t` cancels in `(O.30)`.  This is the graph-level
counterpart of Proof 253's Berezin double-difference identity.

Equation `(O.30)` is not yet a bound: estimating `G_t` separately can recreate
the rejected Euler condition number.  The proposed successor must pair
`(O.22)--(O.26)` with `(O.30)` inside the trace, replace the expanding primal
frame by Proof 255's contractive dual frame where needed, and complete all
crossings before applying Hilbert--Schmidt Cauchy--Schwarz.

The target shape is

```text
abs(complete finite-S response on g)
 <=C (1+B)^d ||g||_(H^s)^2,                           (O.31)
```

for a root supported in `[-B,B]`, uniformly in the visible finite set and the
synchronized parameter.  Equivalently, after a legal prime-power expansion,
every paired channel must have the full `poly(m)p^(-m)` gain of Proof 249.

For the resonant detector sequence there,

```text
B_n=O(n),
||g_n||_(H^s)^2<=fixed_constant*q^(2n),
0<q<1.                                                (O.32)
```

Hence `(O.31)` would imply detector remainder smallness.  An exponential
constant in `B` or a surviving absolute `p^(-m/2)` sum rejects the route.

## 8. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| one-sided inverse-metric factorization         | exact                    |
| conditioned inverse as an independent target  | eliminated               |
| causal oblique coframe                         | exact                    |
| hard-linear/two-crossing split                 | exact                    |
| periodic coframe collapse test                 | invalid model, rejected  |
| finite causal boundary diagnostics             | coherent, nonconvergent  |
| second-boundary/prolate split (O.22)--(O.26)   | exact next organization  |
| synchronized graph equation (O.28)--(O.30)     | exact next organization  |
| uniform polynomial-support estimate (O.31)     | open, active Gate 3      |
| negative-owner integrated smallness            | open                     |
| same-object finite-S trace identity             | open                     |
| Burnol all-zero identity                        | open                     |
| Lean owner or route rewire                      | none                     |
| RH                                              | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 256 removes a false hard bone.  The remaining analytic problem is no
longer a conditioned inverse.  It is one completed two-boundary trace pairing
whose root side is a detector/prolate crossing and whose Euler side is the
scalar-free synchronized graph flow.
