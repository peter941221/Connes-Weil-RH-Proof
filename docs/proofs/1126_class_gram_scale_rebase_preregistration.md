# Record 1126 - class Gram scale normalization and Hbox-G rebase

Date: 2026-09-04.  Status: PRE-REGISTRATION committed before code.

Consumer: the healthy-`CompactLog`, B5-shaped single-window Stage-B chain,
specifically the concrete class-window input to
`C1HboxRationalData.Hbox`, then `C1T2Assembly`, and finally
`C1OrbitWindowSemiLocalGate`.  This is a data-owner brick, not a ROOT-window
or universal B1 campaign.

## 1. Motivation

Record 1125 defines

    G_a[i,j] = integral over R of phi_i^a(x) * phi_j^a(x),

where `phi_i^a(x) = phi_i^1(x/a)`.  The three committed class scales are
`a = 2, 3, 4`.  The exact change of variables therefore gives

    G_a[i,j] = a * G_1[i,j].

This identity is mathematical ownership, not a numerical approximation.  It
lets a later validated base-integral certificate be reused at every class
scale and prevents three copies of the same analytic enclosure obligation.

## 2. Registered targets

1. Prove the pointwise scale identity for the real class-window core.
2. Prove the whole-line Bochner-integral scale identity for
   `classGramEntry`, using the measure change-of-variables theorem and the
   already landed compact-support integrability.
3. Lift the identity to `classGramMatrix` and provide a generic transport
   lemma for entrywise lower/upper bounds into the `Hbox-G` half of `Hbox`.
4. Attempt an exact, source-derived rebase of the committed rational
   `q38`/`q48` G-boxes from the `q28` box.  This may land only if all 64
   entrywise rational comparisons pass in Lean; otherwise the record reports
   the failed comparison and leaves the three-scale boxes independent.

The actual inequalities comparing the real integrals to the `q28` box are
not supplied by this record.  They remain the required validated analytic
certificate, with per-node provenance, for the eventual `Hbox` instance.

## 3. Non-goals and integrity boundary

No floating-point integral, quadrature output, stored conclusion, or
unproved interval claim may enter Lean.  No matrix sign, Stage-B defect
bound, detector-specific semi-local positivity, `SourceRH`, or RH theorem is
claimed.  The record does not invoke the ROOT endpoint or the rejected
normalized additive owner.

## 4. Acceptance gates

G1. The owning module and paired audit module build through the resource
runner with a success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every public declaration printed by the audit has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The scale identities type-check against the exact 1125 Gram owner and
the generic `Hbox` consumer.  Any q38/q48 rebase is accepted only when Lean
checks every finite entry by exact arithmetic.

G4. Staged-diff hygiene finds no private paths, generated build artifacts,
or hidden proof terms.

## 5. Expected consequence

If landed, 1126 does not close `Hbox-G`; it reduces its independent analytic
content to a normalized owner and, if the exact box containment succeeds, to
one base-scale enclosure.  The `(iv)` defect certificate and the final
detector-specific semi-local sign remain open.

RH NOT claimed.
