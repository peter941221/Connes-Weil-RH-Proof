# Proof 434: root-completed homogeneous first jet

Date: 2026-07-20

Status: axiom-clean exact `A^dagger B` owner and homogeneous geometric-energy
estimate for the literal fixed-quotient first jet.  The three compact
half-line kernels also have explicit support-polynomial `0,0` Schwartz
seminorm bounds.

This closes the owner and elementary compact-kernel layers.  The expanded
ledger displays five energies, but only two root legs are independent: `A_0`
is discharged by the existing prolate factor, while `A_2` and `D_1` are
projection suffixes of `A_1` and `D_0`.  It does not yet give the required
family-uniform signed bound, identify the first jet with the completed Burnol
endpoint, close Gate 3U, prove the finite-`S` sign, prove Burnol's identity, or
prove RH.

## 1. Verdict

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| Proof 433 additive energy has correct root scaling   | no                   |
| detector split before taking square energies         | yes                  |
| exact three-branch fixed-quotient identity            | proved               |
| one orthogonal A^dagger B owner for all branches     | constructed          |
| multiplicative geometric-energy trace estimate       | proved               |
| five expanded component energies visible             | yes                  |
| compact half-line kernel support-polynomial bounds    | proved               |
| independent root-leg obligations                     | `A_1`, `D_0`          |
| family-uniform signed root-pair bound                 | not yet              |
| first jet = completed Burnol endpoint                | not proved           |
| Gate 3U / finite-S sign / Burnol / RH                | open                 |
+------------------------------------------------------+----------------------+
```

The advance is the replacement

```text
nonhomogeneous additive energy
  -> split C^dagger C at root level
  -> retain one root in each Hilbert--Schmidt leg
  -> take a geometric mean only after the complete pair exists.       (RC.1)
```

## 2. Scaling obstruction in Proof 433

Let the selected convolution root be `C_g`.  Under scalar rescaling,

```text
g -> epsilon g,
C_g -> epsilon C_g,
W_g=C_g^dagger C_g -> |epsilon|^2 W_g,
actual first-jet response -> |epsilon|^2 response.                     (RC.2)
```

Proof 433 bounds the response by one half of the sum of the two square
energies of `fixedPhysicalPairData`.  Its prolate coordinate contains the
source prolate Hilbert--Schmidt factor independently of one detector-root
scaling.  Consequently that additive energy is not the homogeneous
`|epsilon|^2` quantity needed for a bound by a root seminorm squared.  The
estimate remains a valid visible-family-uniform trace bound, but it is the
wrong analytic target for the next support--Sobolev step.

This is why Proof 434 returns to the earlier two-branch algebra and performs

```text
[L R,Q]=L[R,Q]+[L,Q]R                                  (RC.3)
```

before forming any square energy.

## 3. Exact three-branch owner

Use the actual source maps

```text
B   =sourceBandProjection,
P   =sourceSoninProjection,
Q   =sourceFourierSupportProjection,
L_g =E C_g^dagger,
R_g =C_g E,
N_S =E A_S E.                                         (RC.4)
```

Lean first proves the detector factorization

```text
compressedDetector(E,W_g)=L_g R_g.                    (RC.5)
```

The fixed-quotient corner then has the exact expansion

```text
B [L_g R_g,P] P N_S B

 =B Q L_g R_g P N_S B
  +B(I-Q)L_g[R_g,Q]P N_S B
  +B(I-Q)[L_g,Q]R_g P N_S B.                          (RC.6)
```

The three terms are named by

```lean
rootCompletedSecondSupportCorner
sourceRootCompletedFixedQuotientCorner
sourceFiniteEulerFixedQuotientCorner_eq_rootCompleted
```

in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRootCompletedFirstJet.lean
```

Every summand in `(RC.6)` contains `L_g` once and `R_g` once.  Thus the
operator identity itself has the quadratic root scaling from `(RC.2)`.

## 4. One Hilbert--Schmidt pair

For the three branches define the left and right pair legs

```text
A_0=(B Q L_g)^dagger,             D_0=R_g P N_S B,
A_1=(B(I-Q)L_g)^dagger,           D_1=[R_g,Q]P N_S B,
A_2=(B(I-Q)[L_g,Q])^dagger,       D_2=D_0.             (RC.7)
```

Each branch is literally

```text
A_j^dagger D_j.                                        (RC.8)
```

`sourceRootCompletedPairData` places the three pairs in the orthogonal
carrier

```text
WithLp 2 (H x WithLp 2 (H x H)).                       (RC.9)
```

The theorem

```lean
sourceRootCompletedPairData_traceProduct_eq
```

proves

```text
sourceRootCompletedPairData.traceProduct
  =sourceRootCompletedFixedQuotientCorner.             (RC.10)
```

This is one trace-class owner, not three unrelated diagonal-series claims.

## 5. Multiplicative energy

For any Hilbert--Schmidt pair `(A,D)`, infinite Holder with exponents `2,2`
gives

```text
abs Tr(A^dagger D)
 <=sqrt(sum_i norm(A e_i)^2)
   sqrt(sum_i norm(D e_i)^2).                          (RC.11)
```

The Lean theorem is

```lean
ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy
```

and uses Mathlib's

```lean
Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
Real.HolderConjugate.two_two
```

The orthogonal direct sum exposes the complete bound as

```text
abs Tr(first jet)

 <=sqrt(E(A_0)+E(A_1)+E(A_2))
   sqrt(E(D_0)+E(D_1)+E(D_0)),                         (RC.12)

E(T)=sum_i norm(T e_i)^2.
```

This exact ledger is proved by

```lean
sourceRootCompletedPairData_left_basisEnergy_eq
sourceRootCompletedPairData_right_basisEnergy_eq
sourceRootCompleted_ordinaryTrace_norm_le_explicitGeometricEnergy
```

The reduced consumer additionally proves

```text
abs Tr(first jet)
 <=sqrt(norm(R_g)^2 E(prolateFactor)+2 E(A_1))
   sqrt(3 E(D_0)).                                      (RC.12a)
```

Thus `A_0` is already closed by the source prolate factor, while

```text
A_2=Q A_1,
D_1=(I-Q)D_0                                           (RC.12b)
```

cannot increase square energy.  The five energies in `(RC.12)` are visible
bookkeeping terms, not five independent analytic obligations.

Unlike the additive Proof 433 energy, both square-root factors in `(RC.12)`
scale linearly in `abs(epsilon)`.  Their product therefore scales as
`|epsilon|^2`.

## 6. Compact-kernel polynomial bounds

For a continuous kernel `k : Y x X -> C` with `norm(k)<=M`, Proof 434 proves

```text
sum_i norm(T_k e_i)^2
 <=measure(Y) measure(X) M^2.                          (RC.13)
```

The proof integrates the pointwise square bound and then uses Bessel's
inequality for every finite basis sum.  No unproved Hilbert--Schmidt norm API
is assumed.

For a compact root `g` supported in `[a,c]`, set

```text
d=c-a,
s_00=SchwartzMap.seminorm C 0 0 g.test.                (RC.14)
```

`SchwartzMap.norm_le_seminorm` supplies the pointwise kernel bound.  The
actual interval measures are

```text
measure(BoundaryOutputInterval)=d,
measure(BoundaryNegativeInputInterval)=d,
measure(BoundaryPositiveInputInterval)=d,
measure(BoundaryFullInputInterval)=2d.                 (RC.15)
```

Hence Lean proves

```text
E(negativeBoundaryRootKernel) <=d^2 s_00^2,
E(positiveBoundaryRootKernel) <=d^2 s_00^2,
E(fullBoundaryRootKernel)     <=2 d^2 s_00^2.          (RC.16)
```

The source declarations are

```lean
negativeBoundaryRootKernel_basisEnergy_le_supportPolynomial
positiveBoundaryRootKernel_basisEnergy_le_supportPolynomial
fullBoundaryRootKernel_basisEnergy_le_supportPolynomial
```

These are genuine polynomial support bounds.  They do not by themselves
control the two independent root legs `A_1` and `D_0` in the complete signed
pairing.

## 7. Exact remaining gap

The follow-up normal-form audit in Proof 435 identifies the two independent
legs exactly:

```text
A_1=C_g(B-K_prol),
D_0=C_g P(A_S-I)B.                                    (RC.17)
```

It also proves `A_0=C_g K_prol`, hence

```text
A_0+A_1=C_g B.                                        (RC.18)
```

This changes the next analytic target.  The orthogonal three-coordinate pair
remains a valid fixed-`S` trace-legality witness, but the uniform estimator
must retain the recombined signed pairing

```text
(C_g B)^dagger C_g P(A_S-I)B                          (RC.18a)
```

before the first absolute value.  It must not require separate
Hilbert--Schmidt bounds for `A_1` or for causal renewal atoms.  The separate
same-object endpoint bridge is still required:

```text
fixed-quotient first jet
  -> completed Burnol weighted endpoint / target-commutator response.  (RC.19)
```

Neither the uniform bound for `(RC.18a)` nor `(RC.19)` is stored as a premise
or conclusion in the module.

## 8. Verification

The isolated Ubuntu 24.04 ext4 batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| root-completed first-jet focused axiom audit         |  3259 | PASS   |
| CCM25Concrete aggregate                              |  3709 | PASS   |
| full repository                                      |  3790 | PASS   |
+------------------------------------------------------+-------+--------+
```

The generic ring identities depend on

```text
[propext].                                             (RC.20)
```

Every audited analytic and concrete-carrier theorem depends exactly on

```text
[propext, Classical.choice, Quot.sound].               (RC.21)
```

No project axiom, proof placeholder, `sorryAx`, Gate premise, global
heartbeat increase, or new linter warning was introduced.
