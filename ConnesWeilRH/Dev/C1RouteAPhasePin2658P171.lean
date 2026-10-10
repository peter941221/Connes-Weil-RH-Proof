import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 171 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P171 : ℚ := (922706328472368695176938030593735569988666834925 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P171 : RatPair2542 := ((-2015625526065870109962619109278768183870644917947695660510555380354038394486645822322761664769221 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (706890625410946861394428202006877092903730168276500916803581758749974661527166443414473540051663 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P171 : ℚ := (51267920367123567735500865789132676885699258196525 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P171 :
    phaseExp2646 phaseArg2658P171 20 =
      ((phaseValue2658P171.1,
        phaseValue2658P171.2), phaseRadius2658P171) := by
  decide +kernel

theorem phaseCosPin2658P171 :
    |Real.cos (phaseArg2658P171 : ℝ) -
      (phaseValue2658P171.1 : ℝ)| ≤
        (phaseRadius2658P171 : ℝ) := by
  have hsmall : |((phaseArg2658P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P171]
  have h := phaseExp_cos_error2646 phaseArg2658P171 20 hsmall
  rw [phaseChain2658P171] at h
  simpa [phaseValue2658P171] using h

theorem phaseSinPin2658P171 :
    |Real.sin (phaseArg2658P171 : ℝ) -
      (phaseValue2658P171.2 : ℝ)| ≤
        (phaseRadius2658P171 : ℝ) := by
  have hsmall : |((phaseArg2658P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P171]
  have h := phaseExp_sin_error2646 phaseArg2658P171 20 hsmall
  rw [phaseChain2658P171] at h
  simpa [phaseValue2658P171] using h

end ConnesWeilRH.Dev
