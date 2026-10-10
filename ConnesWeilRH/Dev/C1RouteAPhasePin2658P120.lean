import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 120 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P120 : ℚ := (307568776157456231725646010197911856662888944975 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P120 : RatPair2542 := ((1268795385809652046807376575129535936903288094185844437056383084965081443016104130188394730097611 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (859156401153237557616954396580867322615958335350133201348837118919713139044401647455046394855925 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P120 : ℚ := (29361377514038054947182645338410195353984010858891 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P120 :
    phaseExp2646 phaseArg2658P120 20 =
      ((phaseValue2658P120.1,
        phaseValue2658P120.2), phaseRadius2658P120) := by
  decide +kernel

theorem phaseCosPin2658P120 :
    |Real.cos (phaseArg2658P120 : ℝ) -
      (phaseValue2658P120.1 : ℝ)| ≤
        (phaseRadius2658P120 : ℝ) := by
  have hsmall : |((phaseArg2658P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P120]
  have h := phaseExp_cos_error2646 phaseArg2658P120 20 hsmall
  rw [phaseChain2658P120] at h
  simpa [phaseValue2658P120] using h

theorem phaseSinPin2658P120 :
    |Real.sin (phaseArg2658P120 : ℝ) -
      (phaseValue2658P120.2 : ℝ)| ≤
        (phaseRadius2658P120 : ℝ) := by
  have hsmall : |((phaseArg2658P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P120]
  have h := phaseExp_sin_error2646 phaseArg2658P120 20 hsmall
  rw [phaseChain2658P120] at h
  simpa [phaseValue2658P120] using h

end ConnesWeilRH.Dev
