import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 172 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P172 : ℚ := (934767849105994429754414344719143878093093852375 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P172 : RatPair2542 := ((1567888987821451119092892245237100481021305946772130095444847073191856056657425110549423678012675 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (362643483628413341419987173331928310393494045990333690676598194096892922882592280851711674919475 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P172 : ℚ := (35239766580914267119943956400406683751731210827161 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P172 :
    phaseExp2646 phaseArg2658P172 20 =
      ((phaseValue2658P172.1,
        phaseValue2658P172.2), phaseRadius2658P172) := by
  decide +kernel

theorem phaseCosPin2658P172 :
    |Real.cos (phaseArg2658P172 : ℝ) -
      (phaseValue2658P172.1 : ℝ)| ≤
        (phaseRadius2658P172 : ℝ) := by
  have hsmall : |((phaseArg2658P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P172]
  have h := phaseExp_cos_error2646 phaseArg2658P172 20 hsmall
  rw [phaseChain2658P172] at h
  simpa [phaseValue2658P172] using h

theorem phaseSinPin2658P172 :
    |Real.sin (phaseArg2658P172 : ℝ) -
      (phaseValue2658P172.2 : ℝ)| ≤
        (phaseRadius2658P172 : ℝ) := by
  have hsmall : |((phaseArg2658P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P172]
  have h := phaseExp_sin_error2646 phaseArg2658P172 20 hsmall
  rw [phaseChain2658P172] at h
  simpa [phaseValue2658P172] using h

end ConnesWeilRH.Dev
