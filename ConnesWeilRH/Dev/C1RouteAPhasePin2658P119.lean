import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 119 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P119 : ℚ := (295507255523830497148169696072503548558461927525 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P119 : RatPair2542 := ((-2112291251338178343660966206254775859816428878672401316774436966276507734744529808775741446418751 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (79319877372568119858072623803244887721422244929403544584498230653335503877250930240127463501343 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P119 : ℚ := (18725156341073625938548163164640223323824193332177 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P119 :
    phaseExp2646 phaseArg2658P119 20 =
      ((phaseValue2658P119.1,
        phaseValue2658P119.2), phaseRadius2658P119) := by
  decide +kernel

theorem phaseCosPin2658P119 :
    |Real.cos (phaseArg2658P119 : ℝ) -
      (phaseValue2658P119.1 : ℝ)| ≤
        (phaseRadius2658P119 : ℝ) := by
  have hsmall : |((phaseArg2658P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P119]
  have h := phaseExp_cos_error2646 phaseArg2658P119 20 hsmall
  rw [phaseChain2658P119] at h
  simpa [phaseValue2658P119] using h

theorem phaseSinPin2658P119 :
    |Real.sin (phaseArg2658P119 : ℝ) -
      (phaseValue2658P119.2 : ℝ)| ≤
        (phaseRadius2658P119 : ℝ) := by
  have hsmall : |((phaseArg2658P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P119]
  have h := phaseExp_sin_error2646 phaseArg2658P119 20 hsmall
  rw [phaseChain2658P119] at h
  simpa [phaseValue2658P119] using h

end ConnesWeilRH.Dev
