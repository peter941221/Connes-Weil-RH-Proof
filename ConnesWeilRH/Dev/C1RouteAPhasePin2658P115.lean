import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 115 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P115 : ℚ := (247261172989327558838264439570870316140753857725 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P115 : RatPair2542 := ((15079429649142151929304240640670269082427512663295681255768748514827072228741520707062498000649 / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), (-130047979101610765706512612174281123278198581045691325141364215303746192722933136362789448366573 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536))
def phaseRadius2658P115 : ℚ := (15133367088990180178273368409426262133563159341031 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P115 :
    phaseExp2646 phaseArg2658P115 20 =
      ((phaseValue2658P115.1,
        phaseValue2658P115.2), phaseRadius2658P115) := by
  decide +kernel

theorem phaseCosPin2658P115 :
    |Real.cos (phaseArg2658P115 : ℝ) -
      (phaseValue2658P115.1 : ℝ)| ≤
        (phaseRadius2658P115 : ℝ) := by
  have hsmall : |((phaseArg2658P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P115]
  have h := phaseExp_cos_error2646 phaseArg2658P115 20 hsmall
  rw [phaseChain2658P115] at h
  simpa [phaseValue2658P115] using h

theorem phaseSinPin2658P115 :
    |Real.sin (phaseArg2658P115 : ℝ) -
      (phaseValue2658P115.2 : ℝ)| ≤
        (phaseRadius2658P115 : ℝ) := by
  have hsmall : |((phaseArg2658P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P115]
  have h := phaseExp_sin_error2646 phaseArg2658P115 20 hsmall
  rw [phaseChain2658P115] at h
  simpa [phaseValue2658P115] using h

end ConnesWeilRH.Dev
