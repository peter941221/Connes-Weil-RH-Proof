# Proof 437: paired first jet and quadratic endpoint remainder

Date: 2026-07-20

Status: exact Lean decomposition of the finite-S band endpoint into its two
oriented first-order crossings and a remainder made from paired landing,
coframe, crossing, and missed-range defects.

The result is good but local.  It repairs the direction error left after
Proof 436: an orthogonal Gram endpoint has a forward first jet and its
Hilbert adjoint.  Subtracting only the forward jet leaves a linear term.
Subtracting the Hermitian pair leaves an exact quadratic-product ledger.

This does not yet identify the actual endpoint crossing with the normalized
finite-Euler paired jet, bound the quadratic ledger uniformly, close Gate 3U,
prove the finite-S sign, prove Burnol's identity, or prove RH.

## 1. Verdict

```text
+---------------------------------------------------------+----------------------+
| statement                                               | judgment             |
+---------------------------------------------------------+----------------------+
| actual `B_S-B_0` has a four-block decomposition         | Lean proved          |
| reverse endpoint crossing is the forward adjoint        | Lean proved          |
| diagonal remainder is landing square minus missed square| Lean proved          |
| Gram first jet is forward plus reverse                  | Lean proved          |
| subtracting only the forward jet leaves a linear term   | exact / probe confirms|
| subtracting the paired jet leaves defect products       | Lean proved          |
| completed first-jet trace is `2 Re` of one orientation  | existing Lean theorem|
| reflected outer branch is the missing Euler adjoint     | rejected             |
| actual crossing to normalized-Euler paired-jet bridge   | open                 |
| uniform quadratic-remainder estimate                    | open                 |
| Gate 3U / finite-S sign / Burnol / RH                   | open                 |
+---------------------------------------------------------+----------------------+
```

The corrected flow is

```text
complete Gram endpoint
        |
        +-- forward off-diagonal crossing
        |
        +-- reverse off-diagonal crossing = forward^*
        |
        +-- diagonal landing and missed-range squares
        v
subtract forward + forward^*
        |
        v
only paired defect products remain.                         (PF.1)
```

## 2. Actual projection geometry

On the common logarithmic Hilbert carrier put

```text
E   =radialSupportProjection,
R_0 =sourceSoninProjection,
B_0 =E-R_0,
R_S =targetSoninProjection,
B_S =E-R_S.                                                 (PF.2)
```

Both Sonin projections are absorbed by `E` on the left and right.  Hence
`B_0` and `B_S` are orthogonal projections inside the same support carrier.
Lean proves the exact block decomposition

```text
B_S-B_0
 =R_0 B_S B_0+B_0 B_S R_0
  +R_0 B_S R_0-B_0 R_S B_0.                                (PF.3)
```

The first two terms are off-diagonal relative to

```text
E=B_0+R_0,       B_0 R_0=0,       R_0 B_0=0.               (PF.4)
```

The last two terms have the square form

```text
R_0 B_S R_0=(B_S R_0)^*(B_S R_0),
B_0 R_S B_0=(R_S B_0)^*(R_S B_0).                          (PF.5)
```

Thus the actual formula stored in Lean is

```text
B_S-B_0
 =R_0 B_S B_0+B_0 B_S R_0
  +(B_S R_0)^*(B_S R_0)
  -(R_S B_0)^*(R_S B_0).                                  (PF.6)
```

Only idempotence, self-adjointness, common-support absorption, and `(PF.4)`
enter.  No mixed-projection identity is assumed.

Because all three projections are self-adjoint,

```text
B_0 B_S R_0=(R_0 B_S B_0)^*.                              (PF.7)
```

Equation `(PF.7)` is the missing orientation.  The linear part of an
orthogonal projection variation is necessarily Hermitian.

## 3. Universal Gram endpoint identity

The same direction issue can be seen before specializing to the CCM24
carrier.  Work in an arbitrary noncommutative ring and write

```text
E=B+R,             BR=RB=0,
P=A B C B A^*,     P^2=P,
EP=PE=P.                                                   (PF.8)
```

Here `A` is a transport and `C` is the band Gram inverse.  Define the two
raw first-jet orientations

```text
J_+=R A B,
J_-=B A^* R.                                              (PF.9)
```

At the generic ring layer, `A^*` is notation for the independently supplied
reverse leg.  The concrete Hilbert-carrier theorem then identifies that leg
with the actual adjoint.

Lean proves

```text
P-B
 =J_++J_-
  +J_+(C B A^* B-B)
  +(B A B C-B)J_-
  +J_+ C J_-
  -[B(E-P)][(E-P)B].                                     (PF.10)
```

Every term after `J_++J_-` contains two endpoint defects:

```text
+------------------------------+-----------------------------------------+
| term                         | paired defects                          |
+------------------------------+-----------------------------------------+
| `J_+(C B A^* B-B)`          | forward crossing x coframe defect       |
| `(B A B C-B)J_-`            | reverse coframe defect x crossing       |
| `J_+ C J_-`                 | forward crossing x reverse crossing     |
| `-[B(E-P)][(E-P)B]`         | missed range x missed range             |
+------------------------------+-----------------------------------------+
```

At the identity endpoint these factors vanish in pairs.  This is the exact
meaning of "quadratic remainder" here.  It is an algebraic vanishing-order
statement, not yet a uniform operator-norm or trace estimate.

## 4. Why one orientation is insufficient

For a differentiable path of orthogonal projections,

```text
P(t)^*=P(t)
  => P'(0)^*=P'(0).                                      (PF.11)
```

Relative to `E=B+R`, the first derivative is off-diagonal:

```text
P'(0)=R X B+B X^* R.                                    (PF.12)
```

The second summand is not optional.  Therefore

```text
P(t)-B-t R X B
 =t B X^* R+O(t^2),                                     (PF.13)
```

while

```text
P(t)-B-t(R X B+B X^* R)=O(t^2).                         (PF.14)
```

Proof 436 bounds one oriented detector corner.  The existing repository
already contains the legal Hermitian completion:

```lean
let first := boundedFirstJetPairData targetBasis sourceData band inner transport
BasisHilbertSchmidtPairData.l2Sum first first.swap
```

This is `boundedFirstJetCompletedPairData`.  Its ordinary trace theorem is

```text
Tr(first+first^*)=2 Re Tr(first).                        (PF.15)
```

Thus Proof 436's scalar estimate extends to the paired scalar by the same
factor two.  No new analytic estimate is needed for the adjoint orientation.

## 5. Why reflected outer is not the adjoint Euler jet

The repository's reflected-outer branch belongs to the physical expansion
of the fixed detector commutator.  Its definition is

```lean
(outerCommutatorPairData ...).swap.smulRight (-1)
```

and its trace product is the negative adjoint of the outer commutator branch.
It has detector-boundary ownership.

The missing endpoint orientation instead has Euler-transport ownership:

```text
forward Euler jet =R_0 A_S B_0,
reverse Euler jet =B_0 A_S^* R_0.                       (PF.16)
```

These objects happen to use adjoints, but they answer different questions:

```text
+----------------------+--------------------------+--------------------------+
| object               | varies                   | fixed data               |
+----------------------+--------------------------+--------------------------+
| reflected outer      | detector boundary branch | Euler endpoint           |
| reverse Euler jet    | Gram/Euler endpoint       | detector commutator      |
+----------------------+--------------------------+--------------------------+
```

Replacing `(PF.16)` by the reflected-outer branch confuses a branch inside
`[W,R_0]` with the second orientation of the projection derivative.

## 6. Concrete normalized-Euler paired owner

For

```text
A_S=normalizedFiniteEulerInverse,                       (PF.17)
```

Lean defines

```text
sourceFiniteEulerPairedFirstJet
 =R_0 A_S B_0+B_0 A_S^* R_0
 =R_0 A_S B_0+(R_0 A_S B_0)^*.                         (PF.18)
```

After inserting the compact-root detector, the completed Proof 436 corner is
also stored as

```text
sourceRootCompletedPairedFiniteEulerCorner
 =J_S+J_S^*,                                           (PF.19)

J_S=B_0[W,R_0]R_0 A_S B_0.
```

This gives the correct first-order owner and exposes its scalar trace as a
real Hermitian response.  What is not yet proved is the actual-carrier
identification

```text
R_0 B_S B_0
 =R_0 A_S B_0
  +the corresponding coframe correction.               (PF.20)
```

with the exact CCM24 Gram data and detector insertion used by the Burnol
endpoint.  The universal identity `(PF.10)` gives the required shape, but its
actual producer hypotheses still have to be wired to `(PF.20)`.

## 7. Finite certificate

The reproducible probe is

```text
docs/proofs/437_paired_firstjet_quadratic_remainder_probe.py.  (PF.21)
```

It constructs a random complex transport inside a fixed support space,
forms the exact orthogonal frame projection, and compares one-sided and
paired subtraction over steps `t=2^-2,...,2^-14`.

Command:

```text
python3 docs/proofs/437_paired_firstjet_quadratic_remainder_probe.py
```

Output:

```text
maximum_exact_decomposition_error=1.012818663726e-15
maximum_paired_scalar_error=2.344737338558e-17
smallest-step_single_residual_over_t=6.466270416720e+00
smallest-step_paired_residual_over_t=2.971903029736e-03
paired_residual_quadratic_ratio_spread=1.000385800267e+00
single-to-paired_linear_ratio=2.175801280197e+03

one_sided_remainder=LINEAR
paired_remainder=QUADRATIC
reflected_outer_as_adjoint_jet=REJECTED
gate_3u=OPEN
RH=UNPROVED                                               (PF.22)
```

The exact identity holds to floating-point precision.  At the smallest step,
the one-sided residual divided by `t` remains order one, whereas the paired
residual divided by `t` is already about `0.003`; its residual divided by
`t^2` is stable across the last four steps to a factor `1.00039`.

This probe is a regression certificate, not evidence for Gate 3U or RH.

## 8. Lean ownership

The new source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSPairedFirstJetRemainder.lean.             (PF.23)
```

The central generic declarations are

```lean
endpointProjectionDifference_eq_offDiagonal_add_squareRemainder
inner_gramProjection_band_eq_forward_add_correction
band_gramProjection_inner_eq_reverse_add_correction
inner_gramProjection_inner_eq_two_crossings
gramProjectionDifference_eq_pairedFirstJet_add_quadraticRemainder
```

The actual-carrier declarations are

```lean
targetBandProjection_isStarProjection
soninBandDifference_eq_offDiagonalPair_add_squareRemainder
sourceTargetBand_reverseCrossing_eq_adjoint
sourceTargetBandOffDiagonalPair_eq_forward_add_adjoint
sourceTargetBandSquareRemainder_eq_landingSq_sub_missedSq
sourceFiniteEulerPairedFirstJet_eq_forward_add_adjoint
sourceRootCompletedPairedFiniteEulerCorner_eq_fixedCommutator_add_adjoint
```

The five generic ring theorems use exactly `[propext]`.  The concrete Hilbert
carrier declarations use exactly

```text
[propext, Classical.choice, Quot.sound].                (PF.24)
```

No endpoint estimate or RH conclusion is stored as a premise.

## 9. Remaining route

```text
fixed-commutator one-sided first-jet estimate          CLOSED mathematically
mandatory adjoint orientation                          CLOSED
actual band endpoint block decomposition               CLOSED
generic paired-jet quadratic ledger                    CLOSED
actual endpoint crossing -> normalized-Euler pair      OPEN
coframe-corrected detector identity                    OPEN
uniform canonical-energy bound for quadratic ledger   OPEN
same-object Burnol endpoint                            OPEN
Gate 3U / finite-S sign                                OPEN
Burnol identity                                        OPEN
_root_.RiemannHypothesis                               OPEN
```

The immediate successor must instantiate `(PF.10)` with the actual CCM24
Gram projection and keep the completed detector bracket whole.  Only after
that identification may the canonical Euler energy be used to estimate the
paired remainder.

## 10. Verification

The focused axiom audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSPairedFirstJetRemainderAudit.lean.        (PF.25)
```

The isolated Ubuntu 24.04 ext4 acceptance batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| paired first-jet focused axiom audit                 |  3260 | PASS   |
| CCM25Concrete aggregate                              |  3710 | PASS   |
| full repository                                      |  3791 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit contains `14` `#check` commands and `14` matching
`#print axioms` commands.  The new source and audit contain no `sorry`,
`admit`, or `sorryAx`, add no line longer than 100 characters, and introduce
no new source warning.  The aggregate and full builds replay only pre-existing
warnings from other modules.
