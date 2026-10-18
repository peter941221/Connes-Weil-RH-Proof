import Mathlib.Analysis.Complex.CauchyIntegral

namespace ConnesWeilRH.Dev

noncomputable section

theorem routeBArgumentRadiusConstant2900 :
    (40 : ℝ) / 399 < 3 / 2 := by norm_num

theorem routeBComplexNormOne2900 : ‖(1 : ℂ)‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_one]
  norm_num

theorem routeBReverseTriangle2900 (t : ℂ) :
    1 - ‖t ^ 2‖ ≤ ‖1 - t ^ 2‖ := by
  have h := norm_add_le (1 - t ^ 2) (t ^ 2)
  have h' : ‖(1 : ℂ)‖ ≤ ‖1 - t ^ 2‖ + ‖t ^ 2‖ := by
    simpa [sub_add_cancel] using h
  rw [routeBComplexNormOne2900] at h'
  linarith

theorem routeBSquareNormBound2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) :
    ‖t ^ 2‖ ≤ (1 : ℝ) / 400 := by
  rw [norm_pow]
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg t
  nlinarith

theorem routeBComplexNormTwo2900 : ‖(2 : ℂ)‖ = 2 := by
  rw [Complex.norm_def]
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num [Complex.normSq]

theorem routeBArgumentNormBound2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) (hden : t ^ 2 ≠ 1) :
    ‖2 * t / (1 - t ^ 2)‖ ≤ (40 : ℝ) / 399 := by
  have hsq := routeBSquareNormBound2900 t ht
  have hrev := routeBReverseTriangle2900 t
  have hlower : (399 : ℝ) / 400 ≤ ‖1 - t ^ 2‖ := by
    linarith
  have hpos : 0 < ‖1 - t ^ 2‖ := by positivity
  rw [norm_div, norm_mul, routeBComplexNormTwo2900]
  calc
    2 * ‖t‖ / ‖1 - t ^ 2‖ ≤ 2 * ((1 : ℝ) / 20) / ((399 : ℝ) / 400) := by
      gcongr
    _ = (40 : ℝ) / 399 := by norm_num

theorem routeBDenominatorNonzero2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) : t ^ 2 ≠ 1 := by
  intro hbad
  have hsq := routeBSquareNormBound2900 t ht
  have hone : ‖t ^ 2‖ = 1 := by
    rw [hbad]
    exact routeBComplexNormOne2900
  rw [hone] at hsq
  norm_num at hsq

theorem routeBExpNegOneRealPart2900 (z : ℂ)
    (h : Complex.exp z = -1) : z.re = 0 := by
  have hn := congrArg norm h
  rw [Complex.norm_exp] at hn
  have hneg : ‖(-1 : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq]
    norm_num
  rw [hneg] at hn
  exact (Real.exp_eq_one_iff z.re).mp hn

theorem routeBCoshZeroExpNegOne2900 (z : ℂ)
    (h : Complex.cosh z = 0) : Complex.exp (2 * z) = -1 := by
  rw [Complex.cosh] at h
  have h2 : Complex.exp z + Complex.exp (-z) = 0 := by
    apply (div_eq_zero_iff).mp h |>.resolve_right
    norm_num
  have hm := congrArg (fun w : ℂ => w * Complex.exp z) h2
  dsimp at hm
  rw [add_mul, ← Complex.exp_add, ← Complex.exp_add] at hm
  simp at hm
  exact by simpa [two_mul] using (eq_neg_of_add_eq_zero_left hm)

theorem routeBImaginaryDecomposition2900 (z : ℂ) (hz : z.re = 0) :
    z = z.im * Complex.I := by
  apply Complex.ext <;> simp [hz]

theorem routeBCauchyRemainder2891
    (M : ℝ) (hM0 : 0 ≤ M) (hM : M ≤ 1377903608911726 / 10 ^ 14) :
    M * ((1 : ℝ) / 5) ^ 22 / (1 - (1 : ℝ) / 5) < 1 / 10 ^ 13 := by
  calc
    M * ((1 : ℝ) / 5) ^ 22 / (1 - (1 : ℝ) / 5) ≤
        (1377903608911726 / 10 ^ 14) * ((1 : ℝ) / 5) ^ 22 /
          (1 - (1 : ℝ) / 5) := by
      gcongr
    _ < 1 / 10 ^ 13 := by norm_num

/-- Consumer interface: the analytic bridge supplies the circle supremum bound.
The conclusion is the same rational Cauchy tail, with no numerical value hidden
inside the theorem. -/
theorem routeBCauchyTailOfCircleBound2891
    (circleSup : ℝ) (hSup0 : 0 ≤ circleSup)
    (hSup : circleSup ≤ 1377903608911726 / 10 ^ 14) :
    circleSup * ((1 : ℝ) / 5) ^ 22 / (1 - (1 : ℝ) / 5) < 1 / 10 ^ 13 :=
  routeBCauchyRemainder2891 circleSup hSup0 hSup

end
end ConnesWeilRH.Dev
