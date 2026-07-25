/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization

/-!
# Raw Douglas readout for the completed Julia row

Proof 531 introduced a bounded readout for the recombined raw four-term row.
Proofs 532--535 related that readout to component rows and to the existing
physical Douglas domination contract.

This module records the direct Douglas form of the raw obligation.  The raw
four-term adjoint is dominated by the actual packed physical-analysis column
on every source vector if and only if the bounded raw readout exists.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawDouglasReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Single-suffix raw Douglas contract -/

/-- Direct Douglas domination for the recombined raw four-term adjoint.
The two physical channels stay summed through the actual packed analysis
column. -/
def SuffixRawAmbientBoundaryDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          (‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
            ‖(ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2)

/-- The raw Douglas domination constructs a bounded raw readout on the
genuine packed physical carrier. -/
noncomputable def suffixRawAmbientBoundaryReadoutDataOfDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixRawAmbientBoundaryDomination
      owner lambda p S bound) :
    SuffixRawAmbientBoundaryReadoutData
      owner lambda p S bound := by
  have hpacked : ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 := by
    intro x
    rw [suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels]
    exact hdom.2 x
  let factorWitness := exists_factor_of_norm_sq_le
    ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†)
    (suffixEulerFrameAmbientBoundaryAnalysis lambda p S)
    bound hdom.1 hpacked
  let readout := Classical.choose factorWitness
  have readoutSpec := Classical.choose_spec factorWitness
  exact
    { bound_nonneg := hdom.1
      readout := readout
      readout_norm_le := readoutSpec.1
      factorization := readoutSpec.2 }

/-- Any bounded raw readout is exactly a raw Douglas domination producer.
Thus the readout structure stores no hidden analytic input beyond the
all-vector inequality. -/
theorem SuffixRawAmbientBoundaryReadoutData.domination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryReadoutData
      owner lambda p S bound) :
    SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  have hbound : 0 ≤ bound := data.bound_nonneg
  refine ⟨hbound, ?_⟩
  intro x
  have hnorm :
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)†) x‖ ≤
        bound * ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
    rw [← data.factorization]
    simp only [ContinuousLinearMap.comp_apply]
    calc
      ‖data.readout
          (suffixEulerFrameAmbientBoundaryAnalysis lambda p S x)‖ ≤
          ‖data.readout‖ *
            ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ :=
        data.readout.le_opNorm _
      _ ≤ bound *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
        exact mul_le_mul_of_nonneg_right data.readout_norm_le
          (norm_nonneg _)
  calc
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ^ 2 ≤
        (bound *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hbound (norm_nonneg _))).mpr hnorm
    _ = bound ^ 2 *
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 := by
      rw [mul_pow]
    _ = bound ^ 2 *
        (‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
          ‖(ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2) := by
      rw [suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels]

/-- The direct raw Douglas inequality is equivalent to the bounded raw
readout contract for one suffix. -/
theorem suffixRawAmbientBoundaryDomination_iff_nonempty_readoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixRawAmbientBoundaryDomination owner lambda p S bound ↔
      Nonempty (SuffixRawAmbientBoundaryReadoutData
        owner lambda p S bound) := by
  constructor
  · intro hdom
    exact ⟨suffixRawAmbientBoundaryReadoutDataOfDomination
      owner lambda p S bound hdom⟩
  · rintro ⟨data⟩
    exact SuffixRawAmbientBoundaryReadoutData.domination data

/-! ## Uniform-family raw Douglas contract -/

/-- One raw Douglas bound for every visible-prime/suffix pair. -/
structure SuffixRawAmbientBoundaryUniformDominationData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  domination : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawAmbientBoundaryDomination owner lambda p S bound

/-- A uniform raw Douglas producer gives a uniform raw readout family. -/
noncomputable def
    SuffixRawAmbientBoundaryUniformDominationData.toReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformDominationData
      owner lambda bound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      suffixRawAmbientBoundaryReadoutDataOfDomination owner lambda p S
        bound (data.domination p S) }

/-- Conversely, a uniform raw readout family is already a uniform raw
Douglas producer. -/
noncomputable def
    SuffixRawAmbientBoundaryUniformReadoutData.toDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformReadoutData
      owner lambda bound) :
    SuffixRawAmbientBoundaryUniformDominationData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    domination := fun p S =>
      SuffixRawAmbientBoundaryReadoutData.domination (data.readout p S) }

/-- Uniform raw Douglas domination is equivalent to the uniform raw readout
interface, with the same numerical bound. -/
theorem uniformRawDomination_iff_nonempty_uniformReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixRawAmbientBoundaryUniformDominationData
      owner lambda bound) ↔
      Nonempty (SuffixRawAmbientBoundaryUniformReadoutData
        owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toReadout⟩
  · rintro ⟨data⟩
    exact
      ⟨SuffixRawAmbientBoundaryUniformReadoutData.toDomination data⟩

/-- Existence of some finite uniform raw Douglas bound is exactly existence
of some finite uniform raw readout bound. -/
theorem exists_uniformRawDomination_iff_exists_uniformRawReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformReadoutData
            owner lambda bound)) := by
  constructor
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformRawDomination_iff_nonempty_uniformReadout
        owner lambda bound).mp hdata⟩
  · rintro ⟨bound, hdata⟩
    exact ⟨bound,
      (uniformRawDomination_iff_nonempty_uniformReadout
        owner lambda bound).mpr hdata⟩

/-- The direct raw Douglas interface is equivalent to the component-row
interface at the existence level. -/
theorem exists_uniformRawDomination_iff_exists_uniformComponentReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound)) ↔
      (∃ ambientBound boundaryBound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformComponentReadoutData
            owner lambda ambientBound boundaryBound)) :=
  (exists_uniformRawDomination_iff_exists_uniformRawReadout
    owner lambda).trans
    (exists_uniformComponentReadout_iff_exists_uniformRawReadout
      owner lambda).symm

/-- The direct raw Douglas interface is equivalent to the existing uniform
physical Douglas domination contract. -/
theorem exists_uniformRawDomination_iff_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) :=
  (exists_uniformRawDomination_iff_exists_uniformRawReadout
    owner lambda).trans
    (exists_uniformRawReadout_iff_exists_uniformPhysicalDomination
      owner lambda)

end CCM24FiniteSCompletedJuliaRawDouglasReadout
end CCM25Concrete
end Source
end ConnesWeilRH
