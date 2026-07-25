/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapDouglas
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization

/-!
# Component rows to the direct non-polar Douglas gate

Proof 547 identifies the active Gate 3U producer with the direct non-polar
Douglas estimate.  This module exposes the concrete component-row route into
that gate:

    component rows
      -> packed raw readout
      -> physical mismatch domination
      -> non-polar gap factor
      -> direct non-polar Douglas data.

No component-row producer is constructed here.  The point is to make the
remaining source obligation explicit and quantitative.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaComponentNonpolarDouglas

open CC20Concrete
open CCM24FiniteSCompletedJuliaNonpolarGapDouglas
open CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSProjectionTrace

/-! ## Data-level handoff -/

/-- A uniform component-row package gives the exact direct non-polar gap
Douglas data consumed by Proof 547.  The only added cost is the already
closed polar physical detector norm. -/
noncomputable def
    SuffixRawAmbientBoundaryUniformComponentReadoutData.toNonpolarGapDouglas
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound) :
    SuffixLocalNonpolarGapUniformDouglasData owner lambda
      (‖detectorOperator owner‖ + (ambientBound + boundaryBound)) := by
  let rawReadout := data.toRawUniformReadout
  let mismatchReadout := rawReadout.toMismatch
  let physicalDomination := mismatchReadout.toDomination
  let nonpolarFactor :=
    physicalUniformDominationData_toLocalNonpolarGapUniform
      physicalDomination
  exact SuffixLocalNonpolarGapCoDefectUniformFactorData.toDouglas
    nonpolarFactor

/-- The component-row handoff keeps the expected numerical bound visible. -/
theorem componentReadout_toNonpolarGapDouglas_bound_nonneg
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound) :
    0 ≤ ‖detectorOperator owner‖ + (ambientBound + boundaryBound) := by
  let douglas :=
    SuffixRawAmbientBoundaryUniformComponentReadoutData.toNonpolarGapDouglas
      data
  exact douglas.bound_nonneg

/-- Pointwise readback of the direct Douglas domination obtained from uniform
component rows. -/
theorem componentReadout_toNonpolarGapDouglas_domination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    SuffixLocalNonpolarGapDouglasDomination owner lambda p S
      (‖detectorOperator owner‖ + (ambientBound + boundaryBound)) := by
  let douglas :=
    SuffixRawAmbientBoundaryUniformComponentReadoutData.toNonpolarGapDouglas
      data
  exact douglas.domination p S

/-! ## Existence-level equivalence -/

/-- Uniform component rows are exactly as strong, at the existence level, as
the direct non-polar gap Douglas producer of Proof 547. -/
theorem exists_uniformComponentReadout_iff_exists_uniformNonpolarGapDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound)) ↔
      (∃ bound : ℝ,
        Nonempty
          (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound)) :=
  (exists_uniformComponentReadout_iff_exists_uniformPhysicalDomination
    owner lambda).trans
    (exists_uniformNonpolarGapDouglas_iff_exists_uniformPhysicalDomination
      owner lambda).symm

/-- A concrete component-row producer is enough to enter the final direct
non-polar Douglas gate. -/
theorem exists_uniformComponentReadout_implies_exists_uniformNonpolarGapDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound)) →
      (∃ bound : ℝ,
        Nonempty
          (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound)) :=
  (exists_uniformComponentReadout_iff_exists_uniformNonpolarGapDouglas
    owner lambda).mp

end CCM24FiniteSCompletedJuliaComponentNonpolarDouglas
end CCM25Concrete
end Source
end ConnesWeilRH
