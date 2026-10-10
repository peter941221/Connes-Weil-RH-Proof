import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 075 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P075 : ℚ := (-235199652355701824260788125445462008036326840275 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P075 : RatPair2542 := ((1613122929517898811607915442030738549249623074319341171358402497127573728495362590204187778525559 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-1400098222227921865580315169830949054717653604701973916572648607647787055101596181358607258394353 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576))
def phaseRadius2658P075 : ℚ := (7675855939046681605717650908044294701300385196865 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344)

theorem phaseChain2658P075 :
    phaseExp2646 phaseArg2658P075 20 =
      ((phaseValue2658P075.1,
        phaseValue2658P075.2), phaseRadius2658P075) := by
  decide +kernel

theorem phaseCosPin2658P075 :
    |Real.cos (phaseArg2658P075 : ℝ) -
      (phaseValue2658P075.1 : ℝ)| ≤
        (phaseRadius2658P075 : ℝ) := by
  have hsmall : |((phaseArg2658P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P075]
  have h := phaseExp_cos_error2646 phaseArg2658P075 20 hsmall
  rw [phaseChain2658P075] at h
  simpa [phaseValue2658P075] using h

theorem phaseSinPin2658P075 :
    |Real.sin (phaseArg2658P075 : ℝ) -
      (phaseValue2658P075.2 : ℝ)| ≤
        (phaseRadius2658P075 : ℝ) := by
  have hsmall : |((phaseArg2658P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P075]
  have h := phaseExp_sin_error2646 phaseArg2658P075 20 hsmall
  rw [phaseChain2658P075] at h
  simpa [phaseValue2658P075] using h

end ConnesWeilRH.Dev
