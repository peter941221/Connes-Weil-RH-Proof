# Proof 431: fixed-quotient band-carrier guard

Date: 2026-07-20

Status: a route-facing carrier mismatch is identified and repaired at the
primitive carrier level.  The existing fixed-quotient ambient pair is
meaningful, but its old input-side specialization precomposes both sides with
the source Sonin inclusion.  Its right band leg is therefore identically zero.

The new Lean module constructs the actual closed quotient-band carrier, its
isometric inclusion, and a carrier-correct input-side trace producer obtained
from the existing four-coordinate ambient pair.  Proof 432 subsequently
migrates the current-range Douglas/Julia consumers and separates the actual
source-Sonin Euler schedule from the packed boundary root carrier.  The
physical readout equality and its uniform range-energy estimate remain open.
Gate 3U and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| ambient corner `B[W,R]R A B`                  | meaningful                |
| old input carrier                             | `Ran(R)`                 |
| old right precomposition                      | `B J_R=0`                |
| old input-side response                       | vacuous zero             |
| actual input carrier                          | `Ran(B)`                 |
| closed Hilbert carrier and inclusion           | Lean-owned                |
| corrected input-side trace producer            | axiom-clean               |
| corrected two-branch readback                  | axiom-clean               |
| current-range Julia/Douglas consumers          | migrated in Proof 432     |
| actual physical readout and range energy       | open                      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. The incompatible types

The source Sonin carrier is defined by

```lean
noncomputable abbrev sourceSoninCarrier (lambda : CCM24SoninScale) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule
```

Its inclusion `J_R` has range `Ran(R)`.  Separately, the fixed-quotient band
is

```lean
noncomputable def sourceBandProjection (lambda : CCM24SoninScale) :=
  radialSupportProjection lambda - sourceSoninProjection lambda
```

or, in the mathematical notation used by Proof 405,

```text
B=E-R.                                             (FC.1)
```

Since `R<=E`,

```text
B J_R=(E-R)J_R=J_R-J_R=0.                         (FC.2)
```

The old input-side producer is built with

```lean
boundedPrecomp ... pairData
  (sourceInclusion lambda) (sourceInclusion lambda)
```

while its exact response ends in

```lean
... transport `comp` sourceBandProjection lambda
  `comp` sourceInclusion lambda.
```

Equation `(FC.2)` makes that response zero before any analytic estimate is
used.  A small bound for this object says nothing about the nonzero
fixed-quotient first jet.

## 3. Correct carrier

The new source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSFixedQuotientCarrier.lean
```

It first proves

```text
IsStarProjection(B).                               (FC.3)
```

The proof uses the exact nested-projection identities

```text
R E=R,
R*=R,
E*=E.                                             (FC.4)
```

It then defines

```text
sourceBandClosedRange(lambda)=Ran(B),
sourceBandCarrier(lambda)=the subtype Ran(B),
J_B:sourceBandCarrier(lambda)->finiteSCarrier.    (FC.5)
```

The resulting identities are

```text
J_B* J_B=I,
J_B J_B*=B,
B J_B=J_B.                                        (FC.6)
```

In contrast, the guard theorem proves in Lean

```text
B J_R=0.                                          (FC.7)
```

## 4. Why this is not a cosmetic rename

The fixed quotient is the decomposition

```text
                 fixed outer carrier E H
                           |
              +------------+------------+
              |                         |
          Sonin part                 band part
           Ran(R)                     Ran(B)
              |                         |
             J_R                       J_B
              |                         |
        old producer input       required first-jet input
              |
             B J_R=0.                                    (FC.8)
```

The first jet `B[W,R]R A B` is an endomorphism of the band summand.  Taking a
basis of the Sonin summand is not a harmless coordinate choice; it annihilates
the operator.

## 5. Corrected producer

The new `sourceBandFixedQuotientFirstJetInputSideProducer` performs the
existing bounded precomposition with `J_B` on both sides:

```text
J_B* B[W,R]R A B J_B.                              (FC.9)
```

Because `(FC.6)` holds, `(FC.9)` retains the ambient corner instead of
killing it.  The producer inherits the complete four-coordinate
Hilbert--Schmidt pair and fixed-`S` trace legality.  The theorem
`sourceBandFixedQuotientCorner_eq_secondSupport_twoBranch` also transports
the exact second-support/prolate split to `J_B`.  Proof 432 reconnects:

```text
the current-range Julia consumer to the corrected band producer.   (FC.10)
```

It does so with the rectangular physical input
`J_R^* E A_S E J_B : Ran(B) -> Ran(R)`; it does not identify the packed
boundary root with the source-Sonin Julia carrier.  No theorem quantified over
a `HilbertBasis` of `sourceSoninCarrier` may be counted as a fixed-quotient
trace estimate after this guard.

## 6. Route verdict

```text
What is closed:
  the mismatch is proved rather than inferred from names;
  `Ran(B)` is a closed complete Hilbert carrier;
  its inclusion has the correct projection identities;
  the old Sonin-to-band composition is formally zero.
  the corrected band-carrier input-side producer is trace legal.
  its two-branch second-support/prolate readback is exact.

What remains:
  construct the actual physical right-column readout;
  bound its source-Sonin Julia range energy uniformly in the visible set;
  prove a uniform estimate for that nonzero object;
  close Gate 3U, the finite-S sign, Burnol, and RH.                  (FC.11)
```

## 7. Verification

The focused WSL2 audit passes with `3220` jobs.  All nine audited
declarations depend exactly on

```text
[propext, Classical.choice, Quot.sound].           (FC.12)
```

The audit target is

```text
ConnesWeilRH.Dev.CCM24FiniteSFixedQuotientCarrierAudit.
```

The migrated consumer and its later verification are recorded in
`docs/proofs/432_fixed_quotient_actual_julia_consumer.md`.
