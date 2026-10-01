import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

namespace ConnesWeilRH.Dev.C1RouteAProducerReadback

open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CC20YoshidaNearZeros
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

noncomputable section

def recordedQuartic (rho argument : ℂ) : ℂ :=
  (rho - 1 / 2 - argument) * ((1 - star rho) - 1 / 2 - argument) *
    (star rho - 1 / 2 - argument) * ((1 - rho) - 1 / 2 - argument)

def recordedRootProduct (rho : ℂ) (baseTransform corrTransform : ℂ → ℂ)
    (argument : ℂ) : ℂ :=
  recordedQuartic rho argument * baseTransform (argument + 1 / 2) *
    corrTransform (argument + 1 / 2)

def hermitianReadback (transform : ℂ → ℂ) (argument : ℂ) : ℂ :=
  star (transform (-star argument)) * transform argument

theorem recordedQuartic_target_eq_zero (rho : ℂ) :
    recordedQuartic rho (rho - 1 / 2) = 0 := by
  unfold recordedQuartic
  ring

theorem recordedQuartic_companion_eq_zero (rho : ℂ) :
    recordedQuartic rho ((1 - star rho) - 1 / 2) = 0 := by
  unfold recordedQuartic
  ring

theorem recordedQuartic_eq_source_order (rho argument : ℂ) :
    recordedQuartic rho argument =
      ((1 - rho) - 1 / 2 - argument) * (star rho - 1 / 2 - argument) *
        ((1 - star rho) - 1 / 2 - argument) * (rho - 1 / 2 - argument) := by
  unfold recordedQuartic
  ring

theorem recordedRootProduct_target_eq_zero (rho : ℂ)
    (baseTransform corrTransform : ℂ → ℂ) :
    recordedRootProduct rho baseTransform corrTransform (rho - 1 / 2) = 0 := by
  unfold recordedRootProduct
  rw [recordedQuartic_target_eq_zero]
  simp

theorem recordedRootProduct_companion_eq_zero (rho : ℂ)
    (baseTransform corrTransform : ℂ → ℂ) :
    recordedRootProduct rho baseTransform corrTransform
      ((1 - star rho) - 1 / 2) = 0 := by
  unfold recordedRootProduct
  rw [recordedQuartic_companion_eq_zero]
  simp

theorem recordedRootProduct_pair_readback_eq_zero (rho : ℂ)
    (baseTransform corrTransform : ℂ → ℂ) :
    hermitianReadback (recordedRootProduct rho baseTransform corrTransform)
        (rho - 1 / 2) +
      hermitianReadback (recordedRootProduct rho baseTransform corrTransform)
        ((1 - star rho) - 1 / 2) = 0 := by
  unfold hermitianReadback
  rw [recordedRootProduct_target_eq_zero, recordedRootProduct_companion_eq_zero]
  simp

theorem recordedHermitian_target_eq_zero (rho : ℂ)
    (baseTransform corrTransform : ℂ → ℂ) :
    hermitianReadback (recordedRootProduct rho baseTransform corrTransform)
      (rho - 1 / 2) = 0 := by
  unfold hermitianReadback
  rw [recordedRootProduct_target_eq_zero]
  simp

theorem not_nonnegativeTail_lt_recordedPairGain (rho : ℂ)
    (baseTransform corrTransform : ℂ → ℂ) (tail : ℝ) (htail : 0 ≤ tail) :
    ¬ tail < -(hermitianReadback
        (recordedRootProduct rho baseTransform corrTransform) (rho - 1 / 2) +
      hermitianReadback (recordedRootProduct rho baseTransform corrTransform)
        ((1 - star rho) - 1 / 2)).re := by
  rw [recordedRootProduct_pair_readback_eq_zero]
  simpa using not_lt.mpr htail

theorem selected_square_target_eq_neg_one
    (base correction : CompactLogTest) (iteration : ℕ) (rho : ℂ)
    (htarget : laplaceAt ((convolutionIterate base iteration).convolution correction)
      rho = 1)
    (hcompanion : laplaceAt ((convolutionIterate base iteration).convolution correction)
      (1 - star rho) = -1) :
    laplaceAt (selectedOwner base correction iteration).convolutionSquare
      (rho - 1 / 2) = -1 := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, htarget, hcompanion]
  norm_num

theorem recordedHermitian_ne_selectedSquareTransform
    (baseTransform corrTransform : ℂ → ℂ)
    (base correction : CompactLogTest) (iteration : ℕ) (rho : ℂ)
    (htarget : laplaceAt ((convolutionIterate base iteration).convolution correction)
      rho = 1)
    (hcompanion : laplaceAt ((convolutionIterate base iteration).convolution correction)
      (1 - star rho) = -1) :
    hermitianReadback (recordedRootProduct rho baseTransform corrTransform) ≠
      (fun argument => laplaceAt
        (selectedOwner base correction iteration).convolutionSquare argument) := by
  intro hequal
  have hreadback := congrFun hequal (rho - 1 / 2)
  change hermitianReadback (recordedRootProduct rho baseTransform corrTransform)
      (rho - 1 / 2) = laplaceAt
        (selectedOwner base correction iteration).convolutionSquare (rho - 1 / 2)
    at hreadback
  rw [recordedHermitian_target_eq_zero,
    selected_square_target_eq_neg_one base correction iteration rho
      htarget hcompanion] at hreadback
  norm_num at hreadback

def geometricTailBudget (coefficient : ℝ) (cutoff : ℕ) : ℝ :=
  4 * coefficient * ((3 : ℝ) / 4) ^ cutoff

theorem geometricTailBudget_succ (coefficient : ℝ) (cutoff : ℕ) :
    geometricTailBudget coefficient (cutoff + 1) =
      (3 / 4 : ℝ) * geometricTailBudget coefficient cutoff := by
  unfold geometricTailBudget
  rw [pow_succ]
  ring

theorem geometricTailBudget_growing_coefficient (coefficient : ℝ) (cutoff : ℕ) :
    geometricTailBudget (coefficient * ((4 : ℝ) / 3) ^ cutoff) cutoff =
      4 * coefficient := by
  have hcancel : ((4 : ℝ) / 3) ^ cutoff * ((3 : ℝ) / 4) ^ cutoff = 1 := by
    rw [← mul_pow]
    norm_num
  unfold geometricTailBudget
  calc
    4 * (coefficient * ((4 : ℝ) / 3) ^ cutoff) * ((3 : ℝ) / 4) ^ cutoff =
        4 * coefficient * (((4 : ℝ) / 3) ^ cutoff * ((3 : ℝ) / 4) ^ cutoff) := by
      ring
    _ = 4 * coefficient := by rw [hcancel]; ring

end
end ConnesWeilRH.Dev.C1RouteAProducerReadback
