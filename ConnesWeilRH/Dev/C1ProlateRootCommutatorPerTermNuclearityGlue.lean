/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale

/-!
# C1: per-term nuclearity closure for S2 at unit scale (record 1095)

Record 1094 named the owed analytic contract for S2 as per-term nuclearity of the two
commutator terms `C o K_S` and `K_S o C`.  This record refines that naming to S2's ACTUAL
summands and proves the closure.

The leaf defines (leaf :229) the S2 remainder as

```text
  targetProlateDetectorRootCommutatorRemainder owner family
      = C† ∘ cc20Commutator(C, K_S)
      = C† ∘ (C o K_S - K_S o C)
      = [C† ∘ (C o K_S)]  -  [C† ∘ (K_S o C)]       (comp distributes over sub)
```

so its two summands carry a LEADING `C†`.  Record 1094's contract named the terms WITHOUT
that factor; going from those to S2 would need "bounded left multiplication preserves
IsTraceClassAlong," which is not committed and is false for bare conditional diagonal
summability.  Naming the WITH-`C†` summands instead closes S2 in one line via
`isTraceClassAlong_sub`, with no bare-root contract (#1/#2) at all.

PROBE-P2 measured each raw term nuclear with flat O(1) norm (~4.63, decreasing). Each WITH-`C†`
summand is bounded by that times ‖C‖ (a window-independent constant), so the same flat-O(1)
certification transfers to the named summands unchanged.

This record therefore:
1. NAMES the two S2 summands and their per-term nuclearity as the canonical owed contract,
   `targetProlateDetectorRootCommutatorSandwichedTermNuclearity`.  It is NOT yet discharged in
   Lean - that analytic discharge (plus owner transfer) remains the producer's target.
2. PROVES the glue: S2 follows from that nuclearity alone, by `isTraceClassAlong_sub`, so this
   route needs no bare-root contract and is the canonical closure for the continuum carrier.

RH unclaimed; GATE 1 mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorPerTermNuclearityGlue

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- The first summand of the S2 remainder: `C† ∘ (C ∘ K_S)`. -/
noncomputable def targetProlateDetectorRootCommutatorLeftSummand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  ((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner ∘L
      targetProlateRemainder unitSoninScale family)

/-- The second summand of the S2 remainder: `C† ∘ (K_S ∘ C)`. -/
noncomputable def targetProlateDetectorRootCommutatorRightSummand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  ((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint ∘L
      targetProlateRemainder unitSoninScale family ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)

/-- The S2 remainder is the signed difference of its two named summands. -/
theorem targetProlateDetectorRootCommutatorRemainder_eq_twoSummandDiff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    targetProlateDetectorRootCommutatorRemainder owner family =
      targetProlateDetectorRootCommutatorLeftSummand owner family -
        targetProlateDetectorRootCommutatorRightSummand owner family := by
  ext x
  simp [targetProlateDetectorRootCommutatorRemainder,
    targetProlateDetectorRootCommutatorLeftSummand,
    targetProlateDetectorRootCommutatorRightSummand, cc20Commutator]

/-- PER-TERM NUCLEARITY of the two S2 summands: each has a summable DIAGONAL along the global
basis (= nuclear on the named diagonal), strictly stronger than being Hilbert--Schmidt and equal
to PROBE-P2's flat O(1) up to factor ‖C‖.  The canonical owed analytic contract; not yet
discharged in Lean (producer target). -/
noncomputable def targetProlateDetectorRootCommutatorSandwichedTermNuclearity
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Prop :=
  IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorLeftSummand owner family) ∧
  IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorRightSummand owner family)

/-- S2 closes from per-term nuclearity ALONE, via `isTraceClassAlong_sub`: no bare-root contract
(#1/#2) is needed, so this route sidesteps the false-for-continuum-carrier root-HS premises and is
the canonical closure for the continuum carrier. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_perTermNuclearity
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hnuc : targetProlateDetectorRootCommutatorSandwichedTermNuclearity globalBasis owner family)
      : targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  have hsub : IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorLeftSummand owner family -
        targetProlateDetectorRootCommutatorRightSummand owner family) :=
    isTraceClassAlong_sub globalBasis
      (targetProlateDetectorRootCommutatorLeftSummand owner family)
      (targetProlateDetectorRootCommutatorRightSummand owner family) hnuc.1 hnuc.2
  simpa [targetProlateDetectorRootCommutatorTraceLegality,
    targetProlateDetectorRootCommutatorRemainder_eq_twoSummandDiff] using hsub

end

end C1ProlateRootCommutatorPerTermNuclearityGlue
end Source
end ConnesWeilRH
