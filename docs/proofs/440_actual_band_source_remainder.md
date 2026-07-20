# Proof 440: actual band source-carrier remainder

Date: 2026-07-20

Status: axiom-clean Lean construction of a trace-legal remainder between the
correctly oriented actual-band first jet and the nonlinear source-band Gram
response on one source Sonin carrier.

Lean now owns the carrier and trace-legality ledger for the nonlinear
remainder.  A bound for that remainder and its identification with the
ambient quadratic remainder remain open, along with Gate 3U and RH.

## 1. Verdict

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| first jet is pulled to the source Sonin carrier      | Lean proved          |
| pullback has an explicit Hilbert--Schmidt pair       | Lean proved          |
| pullback keeps the family-free fixed-energy bound    | Lean proved          |
| nonlinear endpoint has a pair on the same carrier    | existing theorem     |
| their difference has an explicit l2Sum pair          | Lean proved          |
| endpoint trace equals first trace minus remainder    | Lean proved          |
| source remainder equals ambient quadratic remainder  | open                 |
| uniform nonlinear-remainder estimate                 | open                 |
| Gate 3U / finite-S sign / Burnol / RH                | open                 |
+------------------------------------------------------+----------------------+
```

## 2. Why a carrier alignment was necessary

Proof 439 owns the correctly oriented first jet on the ambient common-log
Hilbert space.  The existing nonlinear response `sourceBandGramResponse`
lives on the source Sonin carrier.  Subtracting these operators before a
carrier map would be ill-typed, and cycling an ambient trace through a
rectangular inclusion would repeat the trace-anomaly error guarded by Proof
264.

Put

```text
H =finiteSCarrier,
S =sourceSoninCarrier,
J : S -> H =sourceInclusion,
A_S : H -> H =sourceActualBandFiniteEulerPairedResponse,
G_S : S -> S =sourceBandGramResponse.                    (SR.1)
```

Proof 440 first defines the literal source-carrier pullback

```text
F_S=J^* A_S J.                                          (SR.2)
```

Only after `(SR.2)` is formed do both terms have the same domain and codomain:

```text
ambient first jet A_S
        |
        | J^* (.) J
        v
source first jet F_S -----------+
                                |
nonlinear source response G_S --+--> legal subtraction on S.              (SR.3)
```

The construction applies both carrier maps before evaluating the ordinary
trace, so it uses no trace cycle.

## 3. Trace-legal pullback of the first jet

Let `P_A` be Proof 439's `sourceActualBandFiniteEulerPairData`.  It has a
genuine Hilbert--Schmidt pair on the ambient basis and

```text
P_A.traceProduct=A_S.                                   (SR.4)
```

Proof 440 applies `boundedPrecomp` with `J` on both source legs:

```text
P_F=boundedPrecomp(P_A,J,J).                            (SR.5)
```

The generic pair identity gives

```text
P_F.traceProduct=J^* A_S J=F_S.                         (SR.6)
```

The explicit square-summable columns prove
`sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong`; the declaration
stores no separate trace-class premise for `F_S`.

## 4. The family-free bound survives the pullback

The inclusion and all four operators exposed by Proof 439 are contractions:

```text
norm(J)<=1,
norm(R)<=1, norm(B)<=1,
norm(N)<=1, norm(N^*)<=1.                               (SR.7)
```

If the fixed physical pair has energies

```text
E_left =sum_i norm(fixedPair.left(e_i))^2,
E_right=sum_i norm(fixedPair.right(e_i))^2,              (SR.8)
```

then bounded precomposition cannot increase either pulled-back energy.
Proof 439's two ambient branches contribute at most twice `(SR.8)`, and the
trace consumer contributes the matching factor `1/2`.  Lean proves

```text
abs Tr_S(F_S)<=E_left+E_right.                           (SR.9)
```

The right side of `(SR.9)` contains no `family`, so the pullback preserves
Proof 439's visible-family uniformity through `J^*(.)J`.

Proof 434 rules out treating `(SR.9)` as a homogeneous compact-root estimate:
the additive `fixedPhysicalPairData` energy contains an unscaled prolate
coordinate.  Proof 440 transports the bound and leaves that scaling issue
open.

## 5. The same-carrier remainder owner

Define the source-carrier remainder by

```text
D_S=F_S-G_S.                                            (SR.10)
```

The existing `sourceThreeBranchSourcePairData` owns `G_S`.  The generic
`pairDifferenceData` combines its two inputs as

```text
P_D=l2Sum(P_F, P_G.smulRight(-1)).                      (SR.11)
```

Consequently

```text
P_D.traceProduct
 =P_F.traceProduct-P_G.traceProduct
 =F_S-G_S
 =D_S.                                                  (SR.12)
```

Both input pairs have square-summable legs, so the `l2Sum` construction gives
a trace-class owner for the complete difference.  Lean then proves the exact
operator and ordinary-trace ledgers

```text
G_S=F_S-D_S,                                            (SR.13)

Tr_S(G_S)=Tr_S(F_S)-Tr_S(D_S).                          (SR.14)
```

Equation `(SR.14)` uses the trace theorem for a difference of two already
trace-legal operators.  No infinite-dimensional cyclic permutation appears.

## 6. Boundary that remains open

The name `sourceActualBandFiniteEulerRemainderResponse` describes the exact
same-carrier difference `(SR.10)`.  It must not be silently identified with
Proof 438's ambient operator

```text
sourceActualBandQuadraticRemainder.                     (SR.15)
```

That identification still requires a root-sandwiched carrier theorem with a
legal trace bridge.  In particular, Proof 440 proves none of the following:

```text
D_S=J^* sourceActualBandQuadraticRemainder J,
abs Tr_S(D_S)<=canonical Euler energy,
Tr_S(D_S)<=0,
Gate 3U,
_root_.RiemannHypothesis.                               (SR.16)
```

The next estimate must keep the nonlinear source difference whole.  Bounding
the first pair and endpoint pair separately would lose the cancellation that
the new `pairDifferenceData` was introduced to preserve.

## 7. Lean ownership and axioms

The source and focused audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualBandSourceRemainder.lean

ConnesWeilRH/Dev/
  CCM24FiniteSActualBandSourceRemainderAudit.lean.       (SR.17)
```

The central declarations are

```text
sourceActualBandFiniteEulerSoninResponse
sourceActualBandFiniteEulerSoninPairData_traceProduct_eq
sourceActualBandFiniteEulerSonin_ordinaryTrace_norm_le_fixedEnergy
pairDifferenceData_traceProduct_eq
sourceActualBandFiniteEulerRemainderResponse
sourceActualBandFiniteEulerRemainderPairData_traceProduct_eq
sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong
sourceBandGramResponse_eq_soninFirstJet_sub_remainder
ordinaryTraceAlong_sourceBandGramResponse_eq_first_sub_remainder.
```

Every audited declaration uses exactly

```text
[propext, Classical.choice, Quot.sound].                 (SR.18)
```

No project axiom, `sorry`, `admit`, `sorryAx`, stored trace-class premise, or
finite-dimensional trace cycle is introduced.

## 8. Verification

The isolated Ubuntu 24.04 ext4 acceptance batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| actual band source-remainder focused axiom audit     |  3263 | PASS   |
| CCM25Concrete aggregate                              |  3713 | PASS   |
| full repository                                      |  3794 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit contains `15` `#check` commands and `15` matching
`#print axioms` commands.  The new source and audit contain no proof
placeholder, trailing whitespace, or line longer than 100 characters.  The
new source introduces no warning; aggregate and full builds replay only
pre-existing warnings from other modules.

## 9. Remaining bottom

```text
ambient actual first-jet owner                        CLOSED
pullback to the source Sonin carrier                  CLOSED
family-free pullback trace bound                      CLOSED
same-carrier nonlinear remainder owner                CLOSED
ordinary-trace subtraction ledger                     CLOSED
ambient quadratic-remainder identification            OPEN
uniform homogeneous remainder estimate                OPEN
Gate 3U / finite-S sign                               OPEN
Burnol identity                                       OPEN
_root_.RiemannHypothesis                              OPEN
```

The useful successor is a legal root-sandwiched identification of `(SR.10)`
with the actual quadratic endpoint ledger, followed by one uniform estimate
of that complete difference before any branchwise absolute value.
