/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization

/-!
# Physical Douglas readout for the completed Julia mismatch

Proof 506 replaces the adjacent Julia co-defect norm by one genuine
ambient-plus-boundary analysis column.  This module applies the operator-level
Douglas theorem directly to that column.  Under the still-explicit physical
domination premise, it constructs a bounded readout satisfying

```text
readout * physicalAnalysis = mismatch^dagger.
```

Taking adjoints gives the exact synthesis direction

```text
physicalAnalysis^dagger * readout^dagger = mismatch.
```

The converse is also proved, so the readout is exactly a repackaging of the
physical domination condition.  No domination producer or uniform family
bound is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaPhysicalDouglasReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSDouglasFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The genuine physical readout -/

/-- A bounded readout from the actual ambient-plus-boundary carrier whose
composition with physical analysis is the complete signed mismatch adjoint.
The polar and raw rows remain recombined inside that mismatch. -/
structure SuffixMismatchAmbientBoundaryReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  readout :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda
  readout_norm_le : ‖readout‖ ≤ bound
  factorization :
    readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      (suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S)†

/-- The explicit physical domination constructs a readout on the genuine
two-channel carrier.  This is Douglas factorization with
`A=mismatch^dagger` and `B=physicalAnalysis`. -/
noncomputable def suffixMismatchAmbientBoundaryReadoutDataOfDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixMismatchAmbientBoundaryDomination
      owner lambda p S bound) :
    SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound := by
  have hpacked : ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 := by
    intro x
    rw [suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels]
    exact hdom.2 x
  let factorWitness := exists_factor_of_norm_sq_le
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†)
    (suffixEulerFrameAmbientBoundaryAnalysis lambda p S)
    bound hdom.1 hpacked
  let readout := Classical.choose factorWitness
  have readoutSpec := Classical.choose_spec factorWitness
  exact
    { readout := readout
      readout_norm_le := readoutSpec.1
      factorization := readoutSpec.2 }

/-- Adjointing the physical readout recovers the complete mismatch in the
synthesis direction. -/
theorem SuffixMismatchAmbientBoundaryReadoutData.adjoint_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    (suffixEulerFrameAmbientBoundaryAnalysis lambda p S)† ∘L
        (data.readout)† =
      suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] using hadjoint

/-- The synthesis column inherits the same operator-norm bound as the
readout. -/
theorem SuffixMismatchAmbientBoundaryReadoutData.readout_adjoint_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    ‖(data.readout)†‖ ≤ bound := by
  calc
    ‖(data.readout)†‖ = ‖data.readout‖ :=
      ContinuousLinearMap.adjoint.norm_map data.readout
    _ ≤ bound := data.readout_norm_le

/-- A physical zero mode is killed directly by the complete mismatch
adjoint. -/
theorem SuffixMismatchAmbientBoundaryReadoutData.mismatchAdjoint_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound)
    {x : sourceSoninCarrier lambda}
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  rw [← data.factorization]
  simp only [ContinuousLinearMap.comp_apply, hx, map_zero]

/-! ## Exact equivalence with the physical domination -/

/-- Any bounded physical readout implies the original two-channel Douglas
domination.  Thus the readout structure stores no stronger analytic input. -/
theorem SuffixMismatchAmbientBoundaryReadoutData.domination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryReadoutData
      owner lambda p S bound) :
    SuffixMismatchAmbientBoundaryDomination
      owner lambda p S bound := by
  have hbound : 0 ≤ bound := by
    calc
      0 ≤ ‖data.readout‖ := norm_nonneg _
      _ ≤ bound := data.readout_norm_le
  refine ⟨hbound, ?_⟩
  intro x
  have hnorm :
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ≤
        bound *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
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
        exact mul_le_mul_of_nonneg_right data.readout_norm_le (norm_nonneg _)
  calc
    ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
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

/-- Existence of a bounded physical readout is equivalent to the explicit
ambient-plus-boundary domination. -/
theorem suffixMismatchAmbientBoundaryDomination_iff_nonempty_readoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixMismatchAmbientBoundaryDomination owner lambda p S bound ↔
      Nonempty (SuffixMismatchAmbientBoundaryReadoutData
        owner lambda p S bound) := by
  constructor
  · intro hdom
    exact ⟨suffixMismatchAmbientBoundaryReadoutDataOfDomination
      owner lambda p S bound hdom⟩
  · rintro ⟨data⟩
    exact data.domination

end CCM24FiniteSCompletedJuliaPhysicalDouglasReadout
end CCM25Concrete
end Source
end ConnesWeilRH
