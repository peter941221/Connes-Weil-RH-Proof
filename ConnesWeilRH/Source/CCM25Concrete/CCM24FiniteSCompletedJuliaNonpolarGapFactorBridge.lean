/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPolarSlotBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer

/-!
# Non-polar gap factor bridge

Proof 541 names the remaining local non-polar gap factor.  Proofs 511--512
already consume the equivalent local mismatch factor and recover a physical
uniform domination bound with the explicit transition cost `8`.

This module proves the exact bridge between those two interfaces.  It does
not construct the missing factor family or close Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge

open CC20Concrete
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaUniformCoDefectFactor
open CCM24FiniteSCompletedJuliaUniformRawReadout

/-! ## Single-suffix bridge -/

/-- A Proof 541 non-polar gap factor is the existing local mismatch factor.
-/
noncomputable def
    localNonpolarGapFactorData_toMismatchFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectFactorData
      owner lambda p S bound) :
    SuffixMismatchCoDefectFactorData owner lambda p S bound := by
  refine
    { rightFactor := data.completion
      rightFactor_norm_le := data.completion_norm_le
      factorization := ?_ }
  rw [← suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect
    owner lambda p S]
  exact data.factorization

/-- The existing local mismatch factor is the Proof 541 non-polar gap
factor, with the same right-factor norm. -/
noncomputable def
    mismatchFactorData_toLocalNonpolarGapFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchCoDefectFactorData owner lambda p S bound) :
    SuffixLocalNonpolarGapCoDefectFactorData owner lambda p S bound := by
  have hbound : 0 ≤ bound := by
    exact le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  refine
    { bound_nonneg := hbound
      completion := data.rightFactor
      completion_norm_le := data.rightFactor_norm_le
      factorization := ?_ }
  rw [suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect
    owner lambda p S]
  exact data.factorization

/-- The two single-suffix factor interfaces are equivalent at a fixed
bound. -/
theorem localNonpolarGapFactor_iff_mismatchFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    Nonempty (SuffixLocalNonpolarGapCoDefectFactorData
      owner lambda p S bound) ↔
      Nonempty (SuffixMismatchCoDefectFactorData
        owner lambda p S bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨localNonpolarGapFactorData_toMismatchFactor data⟩
  · rintro ⟨data⟩
    exact ⟨mismatchFactorData_toLocalNonpolarGapFactor data⟩

/-! ## Uniform-family bridge -/

/-- Convert the Proof 541 uniform non-polar gap family to the existing
uniform mismatch factor family without changing its bound. -/
noncomputable def
    localNonpolarGapUniformFactorData_toMismatchUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectUniformFactorData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S => localNonpolarGapFactorData_toMismatchFactor
      (data.factor p S) }

/-- Convert the existing uniform mismatch factor family to the Proof 541
non-polar gap family without changing its bound. -/
noncomputable def
    mismatchUniformFactorData_toLocalNonpolarGapUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) :
    SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S => mismatchFactorData_toLocalNonpolarGapFactor
      (data.factor p S) }

/-- Uniform non-polar gap factors and uniform mismatch factors are the same
producer obligation, with the same numerical bound. -/
theorem uniformNonpolarGapFactor_iff_uniformMismatchFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
      owner lambda bound) ↔
      Nonempty (SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
        owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨localNonpolarGapUniformFactorData_toMismatchUniform data⟩
  · rintro ⟨data⟩
    exact ⟨mismatchUniformFactorData_toLocalNonpolarGapUniform data⟩

/-! ## Handoff to the physical owner -/

/-- A uniform non-polar gap factor family reaches the existing physical
domination owner with the explicit transition cost `8`. -/
noncomputable def
    localNonpolarGapUniformFactorData_toUniformDominationEight
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectUniformFactorData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformDominationData owner lambda
      (8 * bound) :=
  SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toUniformDomination_eight
    (localNonpolarGapUniformFactorData_toMismatchUniform data)

/-- A physical uniform domination producer exports the Proof 541 non-polar
gap factor family at the same bound. -/
noncomputable def
    physicalUniformDominationData_toLocalNonpolarGapUniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) :
    SuffixLocalNonpolarGapCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      (mismatchFactorData_toLocalNonpolarGapFactor
        ((SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor
          data).factor p S)) }

/-- Existence of a finite uniform non-polar gap factor is equivalent to
existence of a finite uniform physical domination producer. -/
theorem exists_uniformNonpolarGapFactor_iff_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
        owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨8 * bound,
      ⟨localNonpolarGapUniformFactorData_toUniformDominationEight data⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨bound,
      ⟨physicalUniformDominationData_toLocalNonpolarGapUniform data⟩⟩

end CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
end CCM25Concrete
end Source
end ConnesWeilRH
