# Record 1131: q28 class-Gram interval transfer preregistration

Status: preregistered; implementation pending.

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
