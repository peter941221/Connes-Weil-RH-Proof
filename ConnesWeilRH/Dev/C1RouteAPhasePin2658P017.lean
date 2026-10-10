import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 017 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P017 : ℚ := (-934767849105994429754414344719143878093093852375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P017 : RatPair2542 := ((1567888987821451119092892245237100481021305946772130095444847073191856056657425110549423676609445 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-181321741814206670709993586665964155196747022995166845338299097048446461441296140425855837654803 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072))
def phaseRadius2658P017 : ℚ := (35239766580914267119943956400406683751731210827161 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P017 :
    phaseExp2646 phaseArg2658P017 20 =
      ((phaseValue2658P017.1,
        phaseValue2658P017.2), phaseRadius2658P017) := by
  decide +kernel

theorem phaseCosPin2658P017 :
    |Real.cos (phaseArg2658P017 : ℝ) -
      (phaseValue2658P017.1 : ℝ)| ≤
        (phaseRadius2658P017 : ℝ) := by
  have hsmall : |((phaseArg2658P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P017]
  have h := phaseExp_cos_error2646 phaseArg2658P017 20 hsmall
  rw [phaseChain2658P017] at h
  simpa [phaseValue2658P017] using h

theorem phaseSinPin2658P017 :
    |Real.sin (phaseArg2658P017 : ℝ) -
      (phaseValue2658P017.2 : ℝ)| ≤
        (phaseRadius2658P017 : ℝ) := by
  have hsmall : |((phaseArg2658P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P017]
  have h := phaseExp_sin_error2646 phaseArg2658P017 20 hsmall
  rw [phaseChain2658P017] at h
  simpa [phaseValue2658P017] using h

end ConnesWeilRH.Dev
