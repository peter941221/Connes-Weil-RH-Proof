import Mathlib.Analysis.Complex.CauchyIntegral

namespace ConnesWeilRH.Dev

noncomputable section

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
