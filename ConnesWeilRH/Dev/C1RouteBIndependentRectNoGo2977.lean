import ConnesWeilRH.Dev.C1RouteBDirectZFormula2975
import ConnesWeilRH.Dev.C1RouteBExpRectMembership2963
import ConnesWeilRH.Dev.C1RouteBTSourceNonzero2968

namespace ConnesWeilRH.Dev

noncomputable def routeBNoGoW2977 : ℂ :=
  ((10923 : ℝ) / 10000) - ((1887 : ℝ) / 10000) * Complex.I

noncomputable def routeBNoGoT2977 : ℂ :=
  ((12853 : ℝ) / 500000) - ((21443 : ℝ) / 500000) * Complex.I

theorem routeBIndependentRectNoGo2977 :
    ComplexRect2427.Mem routeBNoGoW2977 routeBLocalStageExpRect2907 ∧
    ComplexRect2427.Mem routeBNoGoT2977 routeBTSourceRect2968 ∧
    (routeBNoGoW2977 + 1 ≠ 0) ∧ routeBNoGoT2977 ≠ 0 ∧
    (((routeBNoGoW2977 - 1) * (routeBNoGoW2977 + 1)⁻¹) /
        routeBNoGoT2977).im >
      ((0.009643062445654370475342615516971944180724636541596131025489457605677501 : ℚ) : ℝ) := by
  have hw : ComplexRect2427.Mem routeBNoGoW2977 routeBLocalStageExpRect2907 := by
    change routeBLocalStageExpRect2907.reLo ≤ routeBNoGoW2977.re ∧
      routeBNoGoW2977.re ≤ routeBLocalStageExpRect2907.reHi ∧
      routeBLocalStageExpRect2907.imLo ≤ routeBNoGoW2977.im ∧
      routeBNoGoW2977.im ≤ routeBLocalStageExpRect2907.imHi
    constructor
    · norm_num [routeBNoGoW2977, routeBLocalStageExpRect2907,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    constructor
    · norm_num [routeBNoGoW2977, routeBLocalStageExpRect2907,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    constructor
    · norm_num [routeBNoGoW2977, routeBLocalStageExpRect2907,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    · norm_num [routeBNoGoW2977, routeBLocalStageExpRect2907,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have ht : ComplexRect2427.Mem routeBNoGoT2977 routeBTSourceRect2968 := by
    change routeBTSourceRect2968.reLo ≤ routeBNoGoT2977.re ∧
      routeBNoGoT2977.re ≤ routeBTSourceRect2968.reHi ∧
      routeBTSourceRect2968.imLo ≤ routeBNoGoT2977.im ∧
      routeBNoGoT2977.im ≤ routeBTSourceRect2968.imHi
    constructor
    · norm_num [routeBNoGoT2977, routeBTSourceRect2968,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    constructor
    · norm_num [routeBNoGoT2977, routeBTSourceRect2968,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    constructor
    · norm_num [routeBNoGoT2977, routeBTSourceRect2968,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    · norm_num [routeBNoGoT2977, routeBTSourceRect2968,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have hwne : routeBNoGoW2977 + 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [routeBNoGoW2977] at him
  have htne : routeBNoGoT2977 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [routeBNoGoT2977] at him
  refine ⟨hw, ht, hwne, htne, ?_⟩
  rw [routeBDirectZImFormula2975 hwne htne]
  norm_num [routeBNoGoW2977, routeBNoGoT2977, Complex.normSq_apply]

end ConnesWeilRH.Dev
