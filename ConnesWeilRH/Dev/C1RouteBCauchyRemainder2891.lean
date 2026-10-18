import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

theorem routeBOddIntegerAbs2900 (k : ℤ) : 1 ≤ |2 * k + 1| := by
  by_cases h : 0 ≤ 2 * k + 1
  · rw [abs_of_nonneg h]
    omega
  · have hn : 2 * k + 1 ≤ -1 := by omega
    rw [abs_of_nonpos (by omega)]
    omega

theorem routeBPiLower2900 : (3 : ℝ) < Real.pi := Real.pi_gt_three

theorem routeBCosineZeroMagnitude2900 (k : ℤ) :
    (3 : ℝ) / 2 ≤ |((2 * k + 1 : ℤ) : ℝ) * Real.pi / 2| := by
  have hk : (1 : ℝ) ≤ |((2 * k + 1 : ℤ) : ℝ)| := by
    exact_mod_cast (routeBOddIntegerAbs2900 k)
  have hp : (3 : ℝ) < Real.pi := routeBPiLower2900
  rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < Real.pi by positivity)]
  nlinarith [abs_nonneg (((2 * k + 1 : ℤ) : ℝ))]

theorem routeBImaginaryNorm2900 (r : ℝ) :
    ‖(r : ℂ) * Complex.I‖ = |r| := by
  have hs : ‖(r : ℂ) * Complex.I‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_I]
    ring_nf
    rw [sq_abs]
  nlinarith [norm_nonneg ((r : ℂ) * Complex.I), abs_nonneg r]

theorem routeBCoshNonzeroSmall2900 (z : ℂ) (hz : ‖z‖ < 3 / 2) :
    Complex.cosh z ≠ 0 := by
  intro hzero
  have hexp := routeBCoshZeroExpNegOne2900 z hzero
  have hreal := routeBExpNegOneRealPart2900 (2 * z) hexp
  have hzreal : z.re = 0 := by simpa using hreal
  have hdecomp := routeBImaginaryDecomposition2900 z hzreal
  rw [hdecomp, Complex.cosh_mul_I] at hzero
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hzero
  have hmag := routeBCosineZeroMagnitude2900 k
  have himag : |z.im| < 3 / 2 := by
    have hnorm : ‖z.im * Complex.I‖ < 3 / 2 := by
      rw [← hdecomp]
      exact hz
    rw [routeBImaginaryNorm2900] at hnorm
    exact hnorm
  have hkeq : z.im = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / 2 := by
    exact_mod_cast hk
  rw [hkeq] at himag
  linarith

theorem routeBComposedCoshNonzero2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) :
    Complex.cosh (2 * t / (1 - t ^ 2)) ≠ 0 := by
  have hden := routeBDenominatorNonzero2900 t ht
  have harg := routeBArgumentNormBound2900 t ht hden
  have hstrict : ‖2 * t / (1 - t ^ 2)‖ < 3 / 2 := by
    linarith [routeBArgumentRadiusConstant2900]
  exact routeBCoshNonzeroSmall2900 _ hstrict

theorem routeBInnerHasDerivAt2900 (t : ℂ) (hden : 1 - t ^ 2 ≠ 0) :
    HasDerivAt (fun x : ℂ => 2 * x / (1 - x ^ 2))
      ((2 * (1 - t ^ 2) - (2 * t) * (-2 * t)) / (1 - t ^ 2) ^ 2) t := by
  have hn : HasDerivAt (fun x : ℂ => 2 * x) 2 t := by
    convert (hasDerivAt_id t).const_mul 2 using 1 <;> simp [id] <;> ring
  have hd : HasDerivAt (fun x : ℂ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℂ)).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id] <;> ring
  convert hn.div hd hden using 1 <;> ring

theorem routeBComposedTanhDifferentiableAt2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) :
    DifferentiableAt ℂ (fun x : ℂ => Complex.tanh (2 * x / (1 - x ^ 2))) t := by
  have hden := routeBDenominatorNonzero2900 t ht
  have hi := routeBInnerHasDerivAt2900 t (sub_ne_zero.mpr (Ne.symm hden))
  have hs := (Complex.hasDerivAt_sinh (2 * t / (1 - t ^ 2))).comp t hi
  have hc := (Complex.hasDerivAt_cosh (2 * t / (1 - t ^ 2))).comp t hi
  have hq := routeBComposedCoshNonzero2900 t ht
  change DifferentiableAt ℂ (fun x : ℂ => Complex.sinh (2 * x / (1 - x ^ 2)) /
    Complex.cosh (2 * x / (1 - x ^ 2))) t
  exact (hs.div hc hq).differentiableAt

/-! The centered quotient used by the Cauchy step.  Centering removes the
removable value at the origin from the later power-series statement. -/
noncomputable def routeBCenteredQ2900 (t : ℂ) : ℂ :=
  (1 + Complex.tanh (2 * t / (1 - t ^ 2))) / 2

theorem routeBCenteredQ_zero2900 : routeBCenteredQ2900 0 = (1 : ℂ) / 2 := by
  simp [routeBCenteredQ2900]

theorem routeBCenteredQ_differentiableAt2900 (t : ℂ)
    (ht : ‖t‖ ≤ (1 : ℝ) / 20) :
    DifferentiableAt ℂ routeBCenteredQ2900 t := by
  have h := routeBComposedTanhDifferentiableAt2900 t ht
  change DifferentiableAt ℂ
    (fun x : ℂ => (1 + Complex.tanh (2 * x / (1 - x ^ 2))) / 2) t
  exact (differentiableAt_const (c := (1 : ℂ)) |>.add h).div_const 2

theorem routeBCenteredQ_neg2900 (t : ℂ) :
    routeBCenteredQ2900 (-t) = 1 - routeBCenteredQ2900 t := by
  rw [routeBCenteredQ2900, routeBCenteredQ2900]
  have harg : 2 * (-t) / (1 - (-t) ^ 2) =
      -(2 * t / (1 - t ^ 2)) := by
    field_simp
  rw [harg, Complex.tanh_neg]
  ring

theorem routeBCenteredQ_hasFPowerSeriesOnBall2900 :
    HasFPowerSeriesOnBall routeBCenteredQ2900
      (cauchyPowerSeries routeBCenteredQ2900 (0 : ℂ) (1 / 20 : NNReal))
      (0 : ℂ) (ENNReal.ofNNReal (1 / 20 : NNReal)) := by
  apply DifferentiableOn.hasFPowerSeriesOnBall
  · intro t ht
    exact (routeBCenteredQ_differentiableAt2900 t
      (mem_closedBall_zero_iff.mp ht)).differentiableWithinAt
  · norm_num

theorem routeBCenteredQ_continuousOn_closedBall2900 :
    ContinuousOn routeBCenteredQ2900
      (Metric.closedBall (0 : ℂ) (1 / 20 : ℝ)) := by
  intro t ht
  exact (routeBCenteredQ_differentiableAt2900 t
    (mem_closedBall_zero_iff.mp ht)).continuousAt.continuousWithinAt

theorem routeBCenteredQ_analyticAt_zero2900 :
    AnalyticAt ℂ routeBCenteredQ2900 0 :=
  routeBCenteredQ_hasFPowerSeriesOnBall2900.analyticAt

theorem routeBCenteredQ_cauchyPowerSeries_coeff_zero2900
    (v : Fin 0 → ℂ) :
    (cauchyPowerSeries routeBCenteredQ2900 (0 : ℂ) (1 / 20 : NNReal)) 0 v =
      (1 : ℂ) / 2 := by
  rw [routeBCenteredQ_hasFPowerSeriesOnBall2900.coeff_zero v]
  exact routeBCenteredQ_zero2900

theorem routeBCenteredQ_hasDerivAt_zero2900 :
    HasDerivAt routeBCenteredQ2900 1 0 := by
  have hi := routeBInnerHasDerivAt2900 (0 : ℂ) (by norm_num)
  have hs := (Complex.hasDerivAt_sinh (2 * (0 : ℂ) / (1 - (0 : ℂ) ^ 2))).comp 0 hi
  have hc := (Complex.hasDerivAt_cosh (2 * (0 : ℂ) / (1 - (0 : ℂ) ^ 2))).comp 0 hi
  have hq := hs.div hc (by simp)
  have hsum := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add hq
  have hhalf := hsum.div_const (2 : ℂ)
  convert hhalf using 1 <;> simp [routeBCenteredQ2900]

theorem routeBCenteredQ_fderiv_zero2900 :
    fderiv ℂ routeBCenteredQ2900 0 = 1 :=
  by
    have h := routeBCenteredQ_hasDerivAt_zero2900.hasFDerivAt.fderiv
    convert h using 1
    ext z
    simp

theorem routeBCenteredQ_fderiv_eq_cauchySeries_deriv2900 :
    fderiv ℂ routeBCenteredQ2900 0 =
      (continuousMultilinearCurryFin1 ℂ ℂ ℂ)
        ((cauchyPowerSeries routeBCenteredQ2900 (0 : ℂ) (1 / 20 : NNReal)).changeOrigin 0 1) := by
  have h := routeBCenteredQ_hasFPowerSeriesOnBall2900.fderiv_eq
    (y := (0 : ℂ)) (by norm_num)
  simpa using h

theorem routeBCenteredQ_cauchySeries_coeff_one2900 :
    (cauchyPowerSeries routeBCenteredQ2900 (0 : ℂ) (1 / 20 : NNReal)).changeOrigin 0 1
      (fun _ => (1 : ℂ)) = 1 := by
  have h := routeBCenteredQ_fderiv_eq_cauchySeries_deriv2900
  rw [routeBCenteredQ_fderiv_zero2900] at h
  have hv := congrArg (fun L => L (1 : ℂ)) h
  simpa using hv.symm

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
