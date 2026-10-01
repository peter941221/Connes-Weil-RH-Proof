import ConnesWeilRH.Dev.C1RouteAAnalyticMomentSystem

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

theorem laplaceAt_one_forces_contraction_cutoff2352
    (base : CompactLogTest) (node : ℂ) (threshold bound : ℝ)
    (hnode : node.re ∈ Set.Icc (0 : ℝ) 1)
    (hvalue : laplaceAt base node = 1) (hbound : bound < 1)
    (hcontract : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ height : ℝ,
      threshold ≤ |height| →
        ‖laplaceAt base ((sigma : ℂ) + (height : ℂ) * Complex.I)‖ ≤ bound) :
    |node.im| < threshold := by
  by_contra houtside
  have hthreshold : threshold ≤ |node.im| := le_of_not_gt houtside
  have hcoordinate : (node.re : ℂ) + (node.im : ℂ) * Complex.I = node := by
    apply Complex.ext <;> simp
  have hreading := hcontract node.re hnode node.im hthreshold
  rw [hcoordinate, hvalue] at hreading
  have hone : (1 : ℝ) ≤ bound := by simpa using hreading
  exact (not_le_of_gt hbound) hone

theorem ownerMomentSolution_forces_contraction_cutoff2352
    (modulations : Fin 30 → ℝ) (nodes target : Fin 30 → ℂ)
    (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det)
    (row : Fin 30) (hnode : (nodes row).re ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target row = 1) (threshold bound : ℝ) (hbound : bound < 1)
    (hcontract : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ height : ℝ,
      threshold ≤ |height| →
        ‖laplaceAt (correctedPhysicalCompactLogTest
          (ownerMomentSolution2351 modulations nodes target) modulations)
          ((sigma : ℂ) + (height : ℂ) * Complex.I)‖ ≤ bound) :
    |(nodes row).im| < threshold := by
  apply laplaceAt_one_forces_contraction_cutoff2352 _ _ _ _ hnode _ hbound hcontract
  rw [ownerMomentSolution2351_realizes _ _ _ hdet, htarget]

end ConnesWeilRH.Dev
