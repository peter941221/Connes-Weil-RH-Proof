import ConnesWeilRH.Dev.C1RouteACellIntegralCharge2675
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2678
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteARepairedOwnerBaseD22682Consumer
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Consumer
import ConnesWeilRH.Dev.C1RouteAOwnerTest
import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684

namespace ConnesWeilRH.Dev

open Set
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open scoped ContDiff

private theorem weightedNormIntervalIntegrable2686
    {f : ℝ → ℂ} {a b sigma : ℝ}
    (hf : Continuous f) :
    IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖f x‖)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.norm

private theorem externalPhysicalContinuous2686
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    Continuous (externalPhysical2344 coefficients modulations) := by
  rw [externalPhysical2344_eq_correctedPhysical]
  exact (correctedPhysical_contDiff coefficients modulations).continuous

private theorem correctedPhysicalSecondDerivativeContinuous2686
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    Continuous (fun x => deriv (deriv (correctedPhysical coefficients modulations)) x) := by
  have hfirst : ContDiff ℝ (1 : WithTop (WithTop ℕ))
      (deriv (correctedPhysical coefficients modulations)) :=
    ContDiff.deriv' ((correctedPhysical_contDiff coefficients modulations).of_le
      (by decide : (2 : WithTop (WithTop ℕ)) ≤ ∞))
  exact hfirst.continuous_deriv (by decide)

theorem weightedFourNormIntegral_le_of_cellRectangles2686
    {fBaseM0 fBaseD2 fCorrectionM0 fCorrectionD2 : ℝ → ℂ}
    {a b sigma weightBound : ℝ}
    (baseM0Rect baseD2Rect correctionM0Rect correctionD2Rect : ComplexRect2427)
    (baseM0Norm baseD2Norm correctionM0Norm correctionD2Norm : ℝ)
    (baseM0Charge baseD2Charge correctionM0Charge correctionD2Charge : ℝ)
    (totalCharge : ℝ)
    (hab : a ≤ b)
    (hBaseM0Rect : ∀ x ∈ Icc a b, baseM0Rect.Mem (fBaseM0 x))
    (hBaseD2Rect : ∀ x ∈ Icc a b, baseD2Rect.Mem (fBaseD2 x))
    (hCorrectionM0Rect : ∀ x ∈ Icc a b,
      correctionM0Rect.Mem (fCorrectionM0 x))
    (hCorrectionD2Rect : ∀ x ∈ Icc a b,
      correctionD2Rect.Mem (fCorrectionD2 x))
    (hBaseM0Norm : baseM0Rect.cornerNorm ≤ baseM0Norm)
    (hBaseD2Norm : baseD2Rect.cornerNorm ≤ baseD2Norm)
    (hCorrectionM0Norm : correctionM0Rect.cornerNorm ≤ correctionM0Norm)
    (hCorrectionD2Norm : correctionD2Rect.cornerNorm ≤ correctionD2Norm)
    (hweight_nonneg : 0 ≤ weightBound)
    (hweight : ∀ x ∈ Icc a b, Real.exp (sigma * x) ≤ weightBound)
    (hBaseM0Price : (b - a) * (weightBound * baseM0Norm) ≤ baseM0Charge)
    (hBaseD2Price : (b - a) * (weightBound * baseD2Norm) ≤ baseD2Charge)
    (hCorrectionM0Price :
      (b - a) * (weightBound * correctionM0Norm) ≤ correctionM0Charge)
    (hCorrectionD2Price :
      (b - a) * (weightBound * correctionD2Norm) ≤ correctionD2Charge)
    (htotalCharge : baseM0Charge + baseD2Charge + correctionM0Charge +
      correctionD2Charge ≤ totalCharge)
    (hBaseM0Continuous : Continuous fBaseM0)
    (hBaseD2Continuous : Continuous fBaseD2)
    (hCorrectionM0Continuous : Continuous fCorrectionM0)
    (hCorrectionD2Continuous : Continuous fCorrectionD2) :
    (∫ x in a..b, Real.exp (sigma * x) * ‖fBaseM0 x‖) +
      (∫ x in a..b, Real.exp (sigma * x) * ‖fBaseD2 x‖) +
      (∫ x in a..b, Real.exp (sigma * x) * ‖fCorrectionM0 x‖) +
      (∫ x in a..b, Real.exp (sigma * x) * ‖fCorrectionD2 x‖) ≤
        totalCharge := by
  have hBaseM0Integrable := weightedNormIntervalIntegrable2686 (sigma := sigma)
    (a := a) (b := b) hBaseM0Continuous
  have hBaseD2Integrable := weightedNormIntervalIntegrable2686 (sigma := sigma)
    (a := a) (b := b) hBaseD2Continuous
  have hCorrectionM0Integrable := weightedNormIntervalIntegrable2686 (sigma := sigma)
    (a := a) (b := b) hCorrectionM0Continuous
  have hCorrectionD2Integrable := weightedNormIntervalIntegrable2686 (sigma := sigma)
    (a := a) (b := b) hCorrectionD2Continuous
  have hBaseM0 := weightedNormIntegral_le_of_cellRectangle hab hBaseM0Rect
    hBaseM0Norm hweight_nonneg hweight hBaseM0Integrable
  have hBaseD2 := weightedNormIntegral_le_of_cellRectangle hab hBaseD2Rect
    hBaseD2Norm hweight_nonneg hweight hBaseD2Integrable
  have hCorrectionM0 := weightedNormIntegral_le_of_cellRectangle hab
    hCorrectionM0Rect hCorrectionM0Norm hweight_nonneg hweight
    hCorrectionM0Integrable
  have hCorrectionD2 := weightedNormIntegral_le_of_cellRectangle hab
    hCorrectionD2Rect hCorrectionD2Norm hweight_nonneg hweight
    hCorrectionD2Integrable
  linarith

theorem weightedFourNormIntegral_le_of_partitionRectangles2686
    {n : ℕ} {endpoint : ℕ → ℝ} {sigma : ℝ}
    {fBaseM0 fBaseD2 fCorrectionM0 fCorrectionD2 : ℝ → ℂ}
    (baseM0Rect baseD2Rect correctionM0Rect correctionD2Rect :
      ℕ → ComplexRect2427)
    (weightBound : ℕ → ℝ)
    (baseM0Norm baseD2Norm correctionM0Norm correctionD2Norm : ℕ → ℝ)
    (baseM0Charge baseD2Charge correctionM0Charge correctionD2Charge :
      ℕ → ℝ)
    (totalCharge : ℕ → ℝ)
    (hendpoint : ∀ k, k < n → endpoint k ≤ endpoint (k + 1))
    (hBaseM0Rect : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (baseM0Rect k).Mem (fBaseM0 x))
    (hBaseD2Rect : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (baseD2Rect k).Mem (fBaseD2 x))
    (hCorrectionM0Rect : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (correctionM0Rect k).Mem (fCorrectionM0 x))
    (hCorrectionD2Rect : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (correctionD2Rect k).Mem (fCorrectionD2 x))
    (hBaseM0Norm : ∀ k, k < n →
      (baseM0Rect k).cornerNorm ≤ baseM0Norm k)
    (hBaseD2Norm : ∀ k, k < n →
      (baseD2Rect k).cornerNorm ≤ baseD2Norm k)
    (hCorrectionM0Norm : ∀ k, k < n →
      (correctionM0Rect k).cornerNorm ≤ correctionM0Norm k)
    (hCorrectionD2Norm : ∀ k, k < n →
      (correctionD2Rect k).cornerNorm ≤ correctionD2Norm k)
    (hweight_nonneg : ∀ k, k < n → 0 ≤ weightBound k)
    (hweight : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      Real.exp (sigma * x) ≤ weightBound k)
    (hBaseM0Price : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) *
        (weightBound k * baseM0Norm k) ≤ baseM0Charge k)
    (hBaseD2Price : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) *
        (weightBound k * baseD2Norm k) ≤ baseD2Charge k)
    (hCorrectionM0Price : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) *
        (weightBound k * correctionM0Norm k) ≤ correctionM0Charge k)
    (hCorrectionD2Price : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) *
        (weightBound k * correctionD2Norm k) ≤ correctionD2Charge k)
    (htotalCharge : ∀ k, k < n →
      baseM0Charge k + baseD2Charge k + correctionM0Charge k +
        correctionD2Charge k ≤ totalCharge k)
    (hBaseM0Continuous : Continuous fBaseM0)
    (hBaseD2Continuous : Continuous fBaseD2)
    (hCorrectionM0Continuous : Continuous fCorrectionM0)
    (hCorrectionD2Continuous : Continuous fCorrectionD2) :
    (∫ x in (endpoint 0)..(endpoint n),
      Real.exp (sigma * x) * ‖fBaseM0 x‖) +
      (∫ x in (endpoint 0)..(endpoint n),
        Real.exp (sigma * x) * ‖fBaseD2 x‖) +
      (∫ x in (endpoint 0)..(endpoint n),
        Real.exp (sigma * x) * ‖fCorrectionM0 x‖) +
      (∫ x in (endpoint 0)..(endpoint n),
        Real.exp (sigma * x) * ‖fCorrectionD2 x‖) ≤
      ∑ k ∈ Finset.range n, totalCharge k := by
  have hBaseM0Integrable : ∀ k, k < n → IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖fBaseM0 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact weightedNormIntervalIntegrable2686 (a := endpoint k)
      (b := endpoint (k + 1)) (sigma := sigma) hBaseM0Continuous
  have hBaseD2Integrable : ∀ k, k < n → IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖fBaseD2 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact weightedNormIntervalIntegrable2686 (a := endpoint k)
      (b := endpoint (k + 1)) (sigma := sigma) hBaseD2Continuous
  have hCorrectionM0Integrable : ∀ k, k < n → IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖fCorrectionM0 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact weightedNormIntervalIntegrable2686 (a := endpoint k)
      (b := endpoint (k + 1)) (sigma := sigma) hCorrectionM0Continuous
  have hCorrectionD2Integrable : ∀ k, k < n → IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖fCorrectionD2 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact weightedNormIntervalIntegrable2686 (a := endpoint k)
      (b := endpoint (k + 1)) (sigma := sigma) hCorrectionD2Continuous
  have hBaseM0 := weightedNormIntegral_le_of_partition2684
    (f := fBaseM0) baseM0Rect weightBound baseM0Norm baseM0Charge
    hendpoint hBaseM0Rect hBaseM0Norm hweight_nonneg hweight
    hBaseM0Integrable hBaseM0Price
  have hBaseD2 := weightedNormIntegral_le_of_partition2684
    (f := fBaseD2) baseD2Rect weightBound baseD2Norm baseD2Charge
    hendpoint hBaseD2Rect hBaseD2Norm hweight_nonneg hweight
    hBaseD2Integrable hBaseD2Price
  have hCorrectionM0 := weightedNormIntegral_le_of_partition2684
    (f := fCorrectionM0) correctionM0Rect weightBound correctionM0Norm
    correctionM0Charge hendpoint hCorrectionM0Rect hCorrectionM0Norm
    hweight_nonneg hweight hCorrectionM0Integrable hCorrectionM0Price
  have hCorrectionD2 := weightedNormIntegral_le_of_partition2684
    (f := fCorrectionD2) correctionD2Rect weightBound correctionD2Norm
    correctionD2Charge hendpoint hCorrectionD2Rect hCorrectionD2Norm
    hweight_nonneg hweight hCorrectionD2Integrable hCorrectionD2Price
  have hcharges :
      (∑ k ∈ Finset.range n, baseM0Charge k) +
        (∑ k ∈ Finset.range n, baseD2Charge k) +
          (∑ k ∈ Finset.range n, correctionM0Charge k) +
            (∑ k ∈ Finset.range n, correctionD2Charge k) =
        ∑ k ∈ Finset.range n,
          (baseM0Charge k + baseD2Charge k + correctionM0Charge k +
            correctionD2Charge k) := by
    simp only [Finset.sum_add_distrib]
  have htotal := Finset.sum_le_sum fun k hk =>
    htotalCharge k (Finset.mem_range.mp hk)
  rw [← hcharges] at htotal
  linarith

/- Record 2686: consume all four repaired-owner rectangle bridges for the
   complete cell-4096 integral charge.  Integrability follows from smoothness. -/

theorem record2686RepairedOwnerCellCharge
    :
    (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2678BaseCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2678BaseCoefficient
            capturedModulations2584)) x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2680CorrectionCoefficient
            capturedModulations2584 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖deriv (deriv (correctedPhysical record2680CorrectionCoefficient
            capturedModulations2584)) x‖) ≤
      (binary64Value2674 0x40c1696a1ea9e753 : ℚ) := by
  apply (weightedFourNormIntegral_le_of_cellRectangles2686
    (a := 0) (b := record2675CellRight) (sigma := (-1 / 2 : ℝ))
    (weightBound := 1)
    record2675BaseM0Rect record2675BaseD2Rect
    record2675CorrectionM0Rect record2675CorrectionD2Rect
    record2675BaseM0Norm record2675BaseD2Norm
    record2675CorrectionM0Norm record2675CorrectionD2Norm
    (binary64Value2674 0x3f97d1ff630bfcb3)
    (binary64Value2674 0x404a7d1a33c7e62d)
    (binary64Value2674 0x4016aa869bbe9eb9)
    (binary64Value2674 0x40c14c14b962bb37)
    (binary64Value2674 0x40c1696a1ea9e753))
  · norm_num [record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · intro x hx
    exact record2678BaseM0CellContained hx
  · intro x hx
    exact record2682RepairedOwnerBaseD2CellContained hx
  · intro x hx
    exact record2680CorrectionM0CellContained hx
  · intro x hx
    exact record2683RepairedOwnerCorrectionD2CellContained hx
  · exact record2675BaseM0CornerNorm
  · exact record2675BaseD2CornerNorm
  · exact record2675CorrectionM0CornerNorm
  · exact record2675CorrectionD2CornerNorm
  · norm_num
  · intro x hx
    exact record2675CellWeightLeOne hx
  · norm_num [record2675CellRight, record2675BaseM0Norm,
      binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675CellRight, record2675BaseD2Norm,
      binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675CellRight, record2675CorrectionM0Norm,
      binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675CellRight, record2675CorrectionD2Norm,
      binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  · exact externalPhysicalContinuous2686 record2678BaseCoefficient
      capturedModulations2584
  · exact correctedPhysicalSecondDerivativeContinuous2686 record2678BaseCoefficient
      capturedModulations2584
  · exact externalPhysicalContinuous2686 record2680CorrectionCoefficient
      capturedModulations2584
  · exact correctedPhysicalSecondDerivativeContinuous2686 record2680CorrectionCoefficient
      capturedModulations2584

end ConnesWeilRH.Dev
