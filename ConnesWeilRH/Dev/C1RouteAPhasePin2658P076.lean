import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 076 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P076 : ℚ := (-223138131722076089683311811320053699931899822825 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P076 : RatPair2542 := ((-124511424293889034409967289958901260799185421645189899947069383173957760679763559676145183530119 / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), (-385242895463635691262057476449871525640093158374758078074437113624208440516913278325662285713111 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P076 : ℚ := (27419601993340365815870325532207078920128898104649 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P076 :
    phaseExp2646 phaseArg2658P076 20 =
      ((phaseValue2658P076.1,
        phaseValue2658P076.2), phaseRadius2658P076) := by
  decide +kernel

theorem phaseCosPin2658P076 :
    |Real.cos (phaseArg2658P076 : ℝ) -
      (phaseValue2658P076.1 : ℝ)| ≤
        (phaseRadius2658P076 : ℝ) := by
  have hsmall : |((phaseArg2658P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P076]
  have h := phaseExp_cos_error2646 phaseArg2658P076 20 hsmall
  rw [phaseChain2658P076] at h
  simpa [phaseValue2658P076] using h

theorem phaseSinPin2658P076 :
    |Real.sin (phaseArg2658P076 : ℝ) -
      (phaseValue2658P076.2 : ℝ)| ≤
        (phaseRadius2658P076 : ℝ) := by
  have hsmall : |((phaseArg2658P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P076]
  have h := phaseExp_sin_error2646 phaseArg2658P076 20 hsmall
  rw [phaseChain2658P076] at h
  simpa [phaseValue2658P076] using h

end ConnesWeilRH.Dev
