import ConnesWeilRH.Dev.C1RouteAThirdCellEndpointAssembly2544

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def cellPolynomial2545 (order : ℕ) (frequency radius near far : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (order + 1),
    (order.choose j : ℝ) * frequency ^ j *
      (bumpNumeratorAbsUpper2536 (order - j) far *
        (1 - near ^ 2)⁻¹ ^ (2 * (order - j)) / radius ^ (order - j))

theorem weightedCell_factor2545 (order : ℕ) (sigma modulation radius near far a b : ℝ) :
    weightedFamilyCellUpper2538 order 1 sigma modulation radius near far a b =
      Real.exp (max (sigma * a) (sigma * b) - 30 * (1 - near ^ 2)⁻¹) *
        cellPolynomial2545 order ‖weightedLambda2537 sigma modulation‖ radius near far := by
  unfold weightedFamilyCellUpper2538 cellPolynomial2545 localCoupledBumpUpper2536
  simp only [norm_one, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sub_eq_add_neg, Real.exp_add]
  ring

theorem cellPolynomial_mono2545 (order : ℕ) {frequency upper radius near far : ℝ}
    (hf : 0 ≤ frequency) (hu : frequency ≤ upper) (hr : 0 < radius)
    (hfar : 0 ≤ far) :
    cellPolynomial2545 order frequency radius near far ≤
      cellPolynomial2545 order upper radius near far := by
  unfold cellPolynomial2545
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf hu j) (by positivity)
  · have hp := bumpNumeratorAbsUpper2536_nonneg (order - j) hfar
    have ht : 0 ≤ (1 - near ^ 2)⁻¹ ^ (2 * (order - j)) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    exact div_nonneg (mul_nonneg hp ht) (pow_nonneg hr.le _)

theorem weightedCell_upper2545 (order : ℕ) (sigma modulation radius near far a b : ℝ)
    {frequency exponential : ℝ} (hr : 0 < radius) (hfar : 0 ≤ far)
    (hf : ‖weightedLambda2537 sigma modulation‖ ≤ frequency)
    (he : Real.exp (max (sigma * a) (sigma * b) - 30 * (1 - near ^ 2)⁻¹) ≤ exponential) :
    weightedFamilyCellUpper2538 order 1 sigma modulation radius near far a b ≤
      exponential * cellPolynomial2545 order frequency radius near far := by
  rw [weightedCell_factor2545]
  have hp := cellPolynomial_mono2545 order (near := near) (norm_nonneg _) hf hr hfar
  have hnonneg : 0 ≤ cellPolynomial2545 order frequency radius near far := by
    unfold cellPolynomial2545
    apply Finset.sum_nonneg
    intro j _
    have hb := bumpNumeratorAbsUpper2536_nonneg (order - j) hfar
    have hu := (norm_nonneg _).trans hf
    have ht : 0 ≤ (1 - near ^ 2)⁻¹ ^ (2 * (order - j)) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    positivity
  exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right he hnonneg)

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.weightedCell_factor2545
#print axioms ConnesWeilRH.Dev.cellPolynomial_mono2545
#print axioms ConnesWeilRH.Dev.weightedCell_upper2545
