/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAnalysisIsometricFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoDefectFactor

/-!
# Canonical physical/JuliA readout bridge

Proof 559 supplied a bounded factor from the actual Julia left co-defect into
the packed physical analysis carrier.  An arbitrary Douglas witness is not
enough for reversing that factor: it may have an invisible component on the
orthogonal complement of the co-defect range.  The range-supported Douglas
construction from `CCM24FiniteSDouglasFactor` removes exactly that ambiguity.

For the actual finite-S step this module records the precise bridge:

```text
raw = leftCoDefect * rightFactor
  <->
physicalReadout * AmbientBoundaryAnalysis = raw†
```

The conversion uses the canonical factor `F` with `F * leftCoDefect =
AmbientBoundaryAnalysis` and `F† * F * leftCoDefect = leftCoDefect`.  The
numerical norm bound is unchanged.  This is a carrier and orientation bridge;
it does not construct the missing raw factor family or prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaCanonicalAnalysisBridge

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaAnalysisIsometricFactor
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawCoDefectFactor
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The canonical actual-step factor -/

/-- The range-supported factor data for the actual two-channel analysis. -/
structure SuffixEulerFrameCanonicalAnalysisFactorData
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) where
  factor : sourceSoninCarrier lambda →L[ℂ]
    suffixEulerFrameAmbientBoundaryCarrier
  factor_norm_le_one : ‖factor‖ ≤ 1
  factorization :
    factor ∘L (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
      suffixEulerFrameAmbientBoundaryAnalysis lambda p S
  adjoint_comp_factor_comp_defect :
    (factor† ∘L factor) ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect

/-- Construct the canonical factor from the exact packed Gram identity. -/
noncomputable def suffixEulerFrameCanonicalAnalysisFactorData
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    SuffixEulerFrameCanonicalAnalysisFactorData lambda p S := by
  let analysis := suffixEulerFrameAmbientBoundaryAnalysis lambda p S
  let defect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  have hnorm : ∀ x : sourceSoninCarrier lambda,
      ‖analysis x‖ = ‖defect x‖ := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [analysis, defect] using
      suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
        lambda p S x
  let witness := exists_range_supported_factor_of_norm_eq analysis defect hnorm
  let factor := Classical.choose witness
  have factorSpec := Classical.choose_spec witness
  exact
    { factor := factor
      factor_norm_le_one := by
        simpa only [factor] using factorSpec.1
      factorization := by
        simpa only [analysis, defect, factor] using factorSpec.2.1
      adjoint_comp_factor_comp_defect := by
        simpa only [analysis, defect, factor] using factorSpec.2.2 }

/-! ## Single-step conversion -/

/-- A raw co-defect factor becomes a readout on the genuine packed physical
analysis carrier. -/
noncomputable def
    rawCoDefectFactor_toCanonicalPhysicalReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawCoDefectFactorData owner lambda p S bound) :
    SuffixRawAmbientBoundaryReadoutData owner lambda p S bound := by
  let analysisData := suffixEulerFrameCanonicalAnalysisFactorData lambda p S
  let readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
    data.rightFactor† ∘L analysisData.factor†
  have hbound : 0 ≤ bound :=
    le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  have hreadout_norm : ‖readout‖ ≤ bound := by
    calc
      ‖readout‖ ≤ ‖data.rightFactor†‖ * ‖analysisData.factor†‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖data.rightFactor‖ * ‖analysisData.factor‖ := by
        calc
          ‖data.rightFactor†‖ * ‖analysisData.factor†‖ =
              ‖data.rightFactor‖ * ‖analysisData.factor†‖ := by
            exact congrArg (fun value : ℝ => value * ‖analysisData.factor†‖)
              (ContinuousLinearMap.adjoint.norm_map data.rightFactor)
          _ = ‖data.rightFactor‖ * ‖analysisData.factor‖ := by
            exact congrArg (fun value : ℝ => ‖data.rightFactor‖ * value)
              (ContinuousLinearMap.adjoint.norm_map analysisData.factor)
      _ ≤ bound * 1 := by
        exact mul_le_mul data.rightFactor_norm_le
          analysisData.factor_norm_le_one (norm_nonneg analysisData.factor)
          hbound
      _ = bound := by ring
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hfactorization :
      readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
        (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† := by
    have hraw := congrArg ContinuousLinearMap.adjoint data.factorization
    calc
      readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
          (data.rightFactor† ∘L analysisData.factor†) ∘L
            (analysisData.factor ∘L
              (suffixEulerFrameSchurStep lambda p S).leftCoDefect) := by
        simp only [readout]
        rw [analysisData.factorization]
      _ = data.rightFactor† ∘L
          ((analysisData.factor† ∘L analysisData.factor) ∘L
            (suffixEulerFrameSchurStep lambda p S).leftCoDefect) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = data.rightFactor† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
        rw [analysisData.adjoint_comp_factor_comp_defect]
      _ = (suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)† := by
        rw [hraw]
        simp only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq]
  exact
    { bound_nonneg := hbound
      readout := readout
      readout_norm_le := hreadout_norm
      factorization := hfactorization }

/-- A physical readout gives a raw co-defect factor through the same
canonical actual-step factor. -/
noncomputable def
    rawPhysicalReadout_toCanonicalCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryReadoutData owner lambda p S bound) :
    SuffixRawCoDefectFactorData owner lambda p S bound := by
  let analysisData := suffixEulerFrameCanonicalAnalysisFactorData lambda p S
  let rightFactor : SourceOp lambda :=
    (data.readout ∘L analysisData.factor)†
  have hbound : 0 ≤ bound := data.bound_nonneg
  have hright_norm : ‖rightFactor‖ ≤ bound := by
    calc
      ‖rightFactor‖ = ‖data.readout ∘L analysisData.factor‖ := by
        simp only [rightFactor]
        exact ContinuousLinearMap.adjoint.norm_map _
      _ ≤ ‖data.readout‖ * ‖analysisData.factor‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 := by
        exact mul_le_mul data.readout_norm_le
          analysisData.factor_norm_le_one (norm_nonneg analysisData.factor)
          hbound
      _ = bound := by ring
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hfactorization :
      suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S =
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L rightFactor := by
    have hread := congrArg ContinuousLinearMap.adjoint data.factorization
    calc
      suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S =
          ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†)† := by
            simp only [ContinuousLinearMap.adjoint_adjoint]
      _ = (data.readout ∘L
          suffixEulerFrameAmbientBoundaryAnalysis lambda p S)† := by
            rw [data.factorization]
      _ = (data.readout ∘L
          (analysisData.factor ∘L
            (suffixEulerFrameSchurStep lambda p S).leftCoDefect))† := by
            rw [analysisData.factorization]
      _ = (suffixEulerFrameSchurStep lambda p S).leftCoDefect† ∘L
          (data.readout ∘L analysisData.factor)† := by
            simp only [ContinuousLinearMap.adjoint_comp,
              ContinuousLinearMap.comp_assoc]
      _ = (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L rightFactor := by
            rw [hself.adjoint_eq]
  exact
    { rightFactor := rightFactor
      rightFactor_norm_le := hright_norm
      factorization := hfactorization }

/-! ## Uniform-family readout bridge -/

noncomputable def
    rawCoDefectUniformFactor_toCanonicalPhysicalReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawCoDefectUniformFactorData owner lambda bound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      rawCoDefectFactor_toCanonicalPhysicalReadout (data.factor p S) }

noncomputable def
    rawPhysicalUniformReadout_toCanonicalCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound) :
    SuffixRawCoDefectUniformFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      rawPhysicalReadout_toCanonicalCoDefectFactor (data.readout p S) }

theorem uniformRawCoDefectFactor_nonempty_iff_uniformPhysicalReadout_nonempty
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixRawCoDefectUniformFactorData owner lambda bound) ↔
      Nonempty (SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨rawCoDefectUniformFactor_toCanonicalPhysicalReadout data⟩
  · rintro ⟨data⟩
    exact ⟨rawPhysicalUniformReadout_toCanonicalCoDefectFactor data⟩

end CCM24FiniteSCompletedJuliaCanonicalAnalysisBridge
end CCM25Concrete
end Source
end ConnesWeilRH
