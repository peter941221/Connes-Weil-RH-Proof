/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor

/-!
# Isometric factorization of the actual two-channel analysis

The ambient antiresonant column and the moving-boundary column have already
been shown to have the Gram operator of the actual Julia `leftCoDefect`.
This module turns that Gram identity into a genuine bounded factorization of
the packed physical analysis column.  The factor is an isometry on the actual
range of `leftCoDefect`; no raw-row or mismatch estimate is inferred.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaAnalysisIsometricFactor

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A bounded lifting of the actual Julia co-defect into the packed physical
analysis carrier. -/
structure SuffixEulerFrameAmbientBoundaryAnalysisFactorData
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) where
  factor : sourceSoninCarrier lambda →L[ℂ]
    suffixEulerFrameAmbientBoundaryCarrier
  factor_norm_le_one : ‖factor‖ ≤ 1
  factorization :
    factor ∘L (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
      suffixEulerFrameAmbientBoundaryAnalysis lambda p S

/-- The Gram equality supplies the exact all-vector norm domination needed by
Douglas.  The argument uses the packed carrier, so the two physical channels
are not estimated separately. -/
noncomputable def
    suffixEulerFrameAmbientBoundaryAnalysisFactorData
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    SuffixEulerFrameAmbientBoundaryAnalysisFactorData lambda p S := by
  let analysis := suffixEulerFrameAmbientBoundaryAnalysis lambda p S
  let defect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  have hnorm : ∀ x : sourceSoninCarrier lambda,
      ‖analysis x‖ = ‖defect x‖ := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [analysis, defect] using
      suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
        lambda p S x
  have hdom : ∀ x : sourceSoninCarrier lambda,
      ‖analysis x‖ ≤ (1 : ℝ) * ‖defect x‖ := by
    intro x
    rw [hnorm x]
    simp
  let witness := CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
    analysis defect 1 zero_le_one hdom
  let factor := Classical.choose witness
  have factorSpec := Classical.choose_spec witness
  exact
    { factor := factor
      factor_norm_le_one := by
        simpa only [factor] using factorSpec.1
      factorization := by
        simpa only [analysis, defect, factor] using factorSpec.2 }

theorem suffixEulerFrameAmbientBoundaryAnalysisFactorData_factor_norm_eq_on_defect
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (data : SuffixEulerFrameAmbientBoundaryAnalysisFactorData lambda p S)
    (x : sourceSoninCarrier lambda) :
    ‖data.factor ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ =
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
  have hfactor := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ]
        suffixEulerFrameAmbientBoundaryCarrier => T x)
    data.factorization
  have hpoint :
      data.factor ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x) =
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S x := by
    simpa only [ContinuousLinearMap.comp_apply] using hfactor
  rw [hpoint]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
    lambda p S x

end CCM24FiniteSCompletedJuliaAnalysisIsometricFactor
end CCM25Concrete
end Source
end ConnesWeilRH
