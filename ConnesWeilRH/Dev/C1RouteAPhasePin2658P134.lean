import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 134 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P134 : ℚ := (476430065028216515810314407953628170124867189275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P134 : RatPair2542 := ((-1966734128796342696409105118386041239964675678569168641576399550433691055606806543763424307773841 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-416652578370123048967545767090340331779872780922523951259428862013147627566386705292506263805253 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P134 : ℚ := (22471291708804305324335252435521889316354143202949 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P134 :
    phaseExp2646 phaseArg2658P134 20 =
      ((phaseValue2658P134.1,
        phaseValue2658P134.2), phaseRadius2658P134) := by
  decide +kernel

theorem phaseCosPin2658P134 :
    |Real.cos (phaseArg2658P134 : ℝ) -
      (phaseValue2658P134.1 : ℝ)| ≤
        (phaseRadius2658P134 : ℝ) := by
  have hsmall : |((phaseArg2658P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P134]
  have h := phaseExp_cos_error2646 phaseArg2658P134 20 hsmall
  rw [phaseChain2658P134] at h
  simpa [phaseValue2658P134] using h

theorem phaseSinPin2658P134 :
    |Real.sin (phaseArg2658P134 : ℝ) -
      (phaseValue2658P134.2 : ℝ)| ≤
        (phaseRadius2658P134 : ℝ) := by
  have hsmall : |((phaseArg2658P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P134]
  have h := phaseExp_sin_error2646 phaseArg2658P134 20 hsmall
  rw [phaseChain2658P134] at h
  simpa [phaseValue2658P134] using h

end ConnesWeilRH.Dev
