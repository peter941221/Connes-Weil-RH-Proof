import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# Actual selected-owner transform interface

This leaf identifies the actual transform weight without introducing the
auxiliary P-only polynomial.  It supplies no Fourier inversion or sign theorem.
-/

namespace ConnesWeilRH.Source.C1RouteASelectedOwnerFourierInterface

open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CC20YoshidaConvolution.CompactLogTest

noncomputable section

theorem selectedOwner_sourceTransform_eq_power_mul
    (base correction : CompactLogTest) (n : Nat) (z : Complex) :
    laplaceAt (selectedOwner base correction n).sourceTest (z - 1 / 2) =
      laplaceAt base z ^ (n + 1) * laplaceAt correction z := by
  rw [selectedOwner_laplaceAt_sourceTest_centered,
    laplaceAt_convolution, laplaceAt_convolutionIterate]

theorem selectedOwner_squareTransform_eq_paired_power_mul
    (base correction : CompactLogTest) (n : Nat) (z : Complex) :
    laplaceAt (selectedOwner base correction n).convolutionSquare (z - 1 / 2) =
      star (laplaceAt base (1 - star z) ^ (n + 1) *
        laplaceAt correction (1 - star z)) *
        (laplaceAt base z ^ (n + 1) * laplaceAt correction z) := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered,
    laplaceAt_convolution, laplaceAt_convolution,
    laplaceAt_convolutionIterate, laplaceAt_convolutionIterate]

theorem selectedOwner_squareTransform_eq_normSq_of_self_pair
    (base correction : CompactLogTest) (n : Nat) (z : Complex)
    (hpair : 1 - star z = z) :
    laplaceAt (selectedOwner base correction n).convolutionSquare (z - 1 / 2) =
      (Complex.normSq (laplaceAt base z ^ (n + 1) * laplaceAt correction z) :
        Complex) := by
  rw [selectedOwner_squareTransform_eq_paired_power_mul, hpair]
  exact Complex.normSq_eq_conj_mul_self.symm

theorem selectedOwner_squareTransform_criticalLine
    (base correction : CompactLogTest) (n : Nat) (frequency : Real) :
    laplaceAt (selectedOwner base correction n).convolutionSquare
        (Complex.I * (frequency : Complex)) =
      (Complex.normSq
        (laplaceAt base (1 / 2 + Complex.I * (frequency : Complex)) ^ (n + 1) *
          laplaceAt correction (1 / 2 + Complex.I * (frequency : Complex))) :
        Complex) := by
  have hpair :
      1 - star (1 / 2 + Complex.I * (frequency : Complex)) =
        (1 / 2 + Complex.I * (frequency : Complex)) := by
    apply Complex.ext <;> simp
    norm_num
  have hcenter :
      (1 / 2 + Complex.I * (frequency : Complex)) - 1 / 2 =
        Complex.I * (frequency : Complex) := by ring
  simpa only [hcenter] using
    selectedOwner_squareTransform_eq_normSq_of_self_pair base correction n
      (1 / 2 + Complex.I * (frequency : Complex)) hpair

end
end ConnesWeilRH.Source.C1RouteASelectedOwnerFourierInterface
