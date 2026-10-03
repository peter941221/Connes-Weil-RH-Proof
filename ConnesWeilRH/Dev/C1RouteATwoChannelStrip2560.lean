import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem correctionSecond_product_le_frozen2560 :
    correctionSecondUpper2343 * baseNormUpper2343 ≤ bUpper2243 := by
  norm_num [correctionSecondUpper2343, baseNormUpper2343, bUpper2243]

theorem frozenStripHypothesis_of_two_compact_endpoint_bounds2560
    (base correction : CompactLogTest) {radius : ℝ}
    (hsuppBase : tsupport (base.test : ℝ → ℂ) ⊆ Set.Icc (-radius) radius)
    (hsuppCorrection : tsupport (correction.test : ℝ → ℂ) ⊆ Set.Icc (-radius) radius)
    (hbase : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (base.test : ℝ → ℂ) ≤ baseNormUpper2343)
    (hcorrectionSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (correction.test : ℝ → ℂ) ≤ correctionSecondUpper2343) :
    FrozenStripHypothesis base correction := by
  have hcSmooth2 : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (correction.test : ℝ → ℂ) :=
    (correction.test.smooth ⊤).of_le (by decide)
  have hcSmoothFirst : ContDiff ℝ (1 : WithTop (WithTop ℕ))
      (deriv (correction.test : ℝ → ℂ)) := ContDiff.deriv' hcSmooth2
  have hc2 : Continuous (deriv (deriv (correction.test : ℝ → ℂ))) :=
    hcSmoothFirst.continuous_deriv (by decide)
  have hbs := (subset_tsupport (base.test : ℝ → ℂ)).trans hsuppBase
  have hcs2 := ((support_deriv_subset (f := deriv (correction.test : ℝ → ℂ))).trans
    (tsupport_deriv_subset (f := (correction.test : ℝ → ℂ)))).trans hsuppCorrection
  intro sigma hsigma
  have hb := stripNorm_le_of_endpoint_bounds (base.test : ℝ → ℂ) base.test.continuous
    hbs hsigma (hbase _ (by simp)) (hbase _ (by simp))
  have hcd := stripSecondNorm_le_of_endpoint_bounds (correction.test : ℝ → ℂ)
    hc2 hcs2 hsigma (hcorrectionSecond _ (by simp)) (hcorrectionSecond _ (by simp))
  exact (min_le_right _ _).trans
    ((mul_le_mul hcd hb (stripNorm_nonneg _ _)
      (by norm_num [correctionSecondUpper2343])).trans correctionSecond_product_le_frozen2560)

theorem frozenStripHypothesis_of_two_external_endpoint_bounds2560
    (baseCoefficients correctionCoefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (hbase : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (externalPhysical2344 baseCoefficients modulations) ≤ baseNormUpper2343)
    (hcorrectionSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (externalPhysical2344 correctionCoefficients modulations) ≤
        correctionSecondUpper2343) :
    FrozenStripHypothesis (correctedPhysicalCompactLogTest baseCoefficients modulations)
      (correctedPhysicalCompactLogTest correctionCoefficients modulations) := by
  apply frozenStripHypothesis_of_two_compact_endpoint_bounds2560
    (correctedPhysicalCompactLogTest baseCoefficients modulations)
    (correctedPhysicalCompactLogTest correctionCoefficients modulations)
    (correctedPhysicalCompactLogTest_tsupport_subset _ _)
    (correctedPhysicalCompactLogTest_tsupport_subset _ _)
  · intro endpoint hendpoint
    simpa only [correctedPhysicalCompactLogTest_toFun, externalPhysical2344_stripNorm_eq]
      using hbase endpoint hendpoint
  · intro endpoint hendpoint
    simpa only [correctedPhysicalCompactLogTest_toFun, externalPhysical2344_stripSecondNorm_eq]
      using hcorrectionSecond endpoint hendpoint

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.correctionSecond_product_le_frozen2560
#print axioms ConnesWeilRH.Dev.frozenStripHypothesis_of_two_compact_endpoint_bounds2560
#print axioms ConnesWeilRH.Dev.frozenStripHypothesis_of_two_external_endpoint_bounds2560
