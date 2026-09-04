# Record 1131: q28 class-Gram interval transfer preregistration

Status: landed as a conditional interval-transfer consumer; the actual
base-moment producer and M-side enclosure remain pending.

Consumer: the healthy-`CompactLog`, B5-shaped detector-specific semi-local
chain, through the true-data class-window `Hbox-G` input consumed by
`C1T2Assembly`.

## 1. Purpose

Record 1130 reduced the complete first-eight unit class Gram matrix to the
actual base moments

```text
I₀ = classMoment 0,    I₂ = classMoment 2.
```

The q28 certificate is the scale-`a = 2` box.  This record installs the
missing exact interval-transfer consumer: explicit rational intervals for
`I₀` and `I₂` imply entrywise containment of the scaled moment model in the
committed q28 `GLo/GHi` box.

The intervals are deliberately an interface.  Their containment of the
actual integrals remains a separate producer obligation; this record must not
turn the q28 numerical bundle into a proof of those inequalities.

## 2. Registered targets

1. Define the explicit rational base intervals

   ```text
   I₀ ∈ [2397466416982805/18014398509481984 ± 1/10^15],
   I₂ ∈ [8817094793947821/576460752303423488 ± 1/10^15].
   ```

2. Prove, with exact rational arithmetic, that these two interval hypotheses
   imply for every `i,j : Fin 8`

   ```text
   GLo_q28 i j ≤
     2 * classGramMomentModel I₀ I₂ i j ≤ GHi_q28 i j.
   ```

3. Provide the Hbox-facing adapter only conditionally on an independently
   supplied q28 M-side enclosure.  It must use the actual
   `classGramMatrix 2` owner through the scale identity, not a stored Gram
   matrix.

## 3. Integrity and scope

All interval implications are exact real inequalities.  No quadrature output,
floating-point midpoint, asserted base-moment enclosure, M-side enclosure,
`Hbox`, `(iv)` defect estimate, detector-specific positivity, `SourceRH`, or
RH theorem is claimed by this record.  The displayed intervals are chosen as
conditional input slots around the q28 box center; a later analytic producer
must prove that the actual `classBump^2` integrals lie inside them.

The record serves the healthy-`CompactLog` B5 consumer.  It does not create a
universal B1 theorem, a density lift, a ROOT-to-detector arrow, or a
normalized additive-owner result.

## 4. Acceptance gates

G1. The owning and paired audit modules build through the resource runner with
the success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every audited declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The q28 bound theorem unfolds `classGramMomentModel` and uses only the
explicit interval hypotheses plus exact rational inequalities; no theorem
asserting actual membership in either interval may be imported as a hidden
premise.

G4. The scale-2 bridge reads through `classGramMatrix_scale` and the actual
`classGramMatrix 2`, with no replacement by committed `Q28.G` data.

G5. Staged-diff hygiene finds no private paths, generated build artifacts, or
hidden proof terms.

RH NOT claimed.

## 5. Post-run addendum (2026-09-05, after build 4)

VERDICT: LANDED (CONDITIONAL CONSUMER).

The paired modules `C1Q28ClassGramIntervalTransfer.lean` and
`C1Q28ClassGramIntervalTransferAudit.lean` implement all three registered
consumer targets.  The model theorem proves the 64 q28 entrywise inequalities
from the four explicit rational endpoint hypotheses.  The owner theorem then
uses `classGramUnitMatrix_eq_classGramMomentModel` and
`classGramMatrix_scale` at `a = 2` to transfer those bounds to the actual
`classGramMatrix 2`; it does not substitute the committed `Q28.G` matrix.
The Hbox adapter remains conditional on an independently supplied q28 M-side
entrywise bound.

Build-4 evidence is the ext4-mirror log `1131_build4.log`: success footer
`Build completed successfully (3660 jobs)`, zero `^error:` lines, zero
`sorryAx`, and zero warnings from the two 1131 modules.  The audit contains
seven unique declaration records, all with exactly
`[propext, Classical.choice, Quot.sound]`.

The actual membership statements
`q28Moment0Lo ≤ classMoment 0 ≤ q28Moment0Hi` and
`q28Moment2Lo ≤ classMoment 2 ≤ q28Moment2Hi` are not proved here.  Therefore
the q28 `Hbox-G` leg is still an open analytic producer obligation, as is the
M-side enclosure.  The 1116c defect estimate, same-detector semi-local
positivity, `SourceRH`, and RH remain open.

The route boundary is unchanged: this is a conditional algebraic consumer
for the healthy-`CompactLog` B5 chain, not a universal B1 result, density
lift, ROOT-to-detector arrow, or RH claim.
