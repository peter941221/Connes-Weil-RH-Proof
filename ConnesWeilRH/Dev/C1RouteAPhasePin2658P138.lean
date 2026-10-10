import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 138 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P138 : ℚ := (524676147562719454120219664455261402542575259075 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P138 : RatPair2542 := ((-50831109054633713759357356539840128123135195568886436187201600370147271625674059829148793922099 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (1067691062055694923611178651722720293514694497356079381417066512749323311638445799143713806618305 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P138 : ℚ := (11174912881359020198501396157383199620516687366211 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P138 :
    phaseExp2646 phaseArg2658P138 20 =
      ((phaseValue2658P138.1,
        phaseValue2658P138.2), phaseRadius2658P138) := by
  decide +kernel

theorem phaseCosPin2658P138 :
    |Real.cos (phaseArg2658P138 : ℝ) -
      (phaseValue2658P138.1 : ℝ)| ≤
        (phaseRadius2658P138 : ℝ) := by
  have hsmall : |((phaseArg2658P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P138]
  have h := phaseExp_cos_error2646 phaseArg2658P138 20 hsmall
  rw [phaseChain2658P138] at h
  simpa [phaseValue2658P138] using h

theorem phaseSinPin2658P138 :
    |Real.sin (phaseArg2658P138 : ℝ) -
      (phaseValue2658P138.2 : ℝ)| ≤
        (phaseRadius2658P138 : ℝ) := by
  have hsmall : |((phaseArg2658P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P138]
  have h := phaseExp_sin_error2646 phaseArg2658P138 20 hsmall
  rw [phaseChain2658P138] at h
  simpa [phaseValue2658P138] using h

end ConnesWeilRH.Dev
