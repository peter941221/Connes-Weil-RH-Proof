import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 072 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P072 : ℚ := (-271384214256579027993217067821686932349607892625 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P072 : RatPair2542 := ((90607291886270538683504970750502893401938584519581765704808202676109432865465987204333612373027 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-1568681673834259947082724415685418932886503355318735946213517305578162810222438198915805806752065 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P072 : ℚ := (1505635665543431328370311162010610176952624299645 / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336)

theorem phaseChain2658P072 :
    phaseExp2646 phaseArg2658P072 20 =
      ((phaseValue2658P072.1,
        phaseValue2658P072.2), phaseRadius2658P072) := by
  decide +kernel

theorem phaseCosPin2658P072 :
    |Real.cos (phaseArg2658P072 : ℝ) -
      (phaseValue2658P072.1 : ℝ)| ≤
        (phaseRadius2658P072 : ℝ) := by
  have hsmall : |((phaseArg2658P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P072]
  have h := phaseExp_cos_error2646 phaseArg2658P072 20 hsmall
  rw [phaseChain2658P072] at h
  simpa [phaseValue2658P072] using h

theorem phaseSinPin2658P072 :
    |Real.sin (phaseArg2658P072 : ℝ) -
      (phaseValue2658P072.2 : ℝ)| ≤
        (phaseRadius2658P072 : ℝ) := by
  have hsmall : |((phaseArg2658P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P072]
  have h := phaseExp_sin_error2646 phaseArg2658P072 20 hsmall
  rw [phaseChain2658P072] at h
  simpa [phaseValue2658P072] using h

end ConnesWeilRH.Dev
