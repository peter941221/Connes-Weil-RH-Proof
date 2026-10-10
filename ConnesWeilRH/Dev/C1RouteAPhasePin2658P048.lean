import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 048 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P048 : ℚ := (-560860709463596657852648606831486326855856311425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P048 : RatPair2542 := ((-284883538657788454998007050908300433429458503322013612903337596510480454097536643624417908726519 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-2116903868158403542950260745739500343436483985352155766928681614217215997229534942876078075389029 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P048 : ℚ := (14049551274616795582053412067981333044812670480355 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P048 :
    phaseExp2646 phaseArg2658P048 20 =
      ((phaseValue2658P048.1,
        phaseValue2658P048.2), phaseRadius2658P048) := by
  decide +kernel

theorem phaseCosPin2658P048 :
    |Real.cos (phaseArg2658P048 : ℝ) -
      (phaseValue2658P048.1 : ℝ)| ≤
        (phaseRadius2658P048 : ℝ) := by
  have hsmall : |((phaseArg2658P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P048]
  have h := phaseExp_cos_error2646 phaseArg2658P048 20 hsmall
  rw [phaseChain2658P048] at h
  simpa [phaseValue2658P048] using h

theorem phaseSinPin2658P048 :
    |Real.sin (phaseArg2658P048 : ℝ) -
      (phaseValue2658P048.2 : ℝ)| ≤
        (phaseRadius2658P048 : ℝ) := by
  have hsmall : |((phaseArg2658P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P048]
  have h := phaseExp_sin_error2646 phaseArg2658P048 20 hsmall
  rw [phaseChain2658P048] at h
  simpa [phaseValue2658P048] using h

end ConnesWeilRH.Dev
