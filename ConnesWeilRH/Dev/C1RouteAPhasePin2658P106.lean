import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 106 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P106 : ℚ := (138707487286695947640977612442195543200910700675 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P106 : RatPair2542 := ((-108787871429139788065266020956452974189796446974656124985020666059257180341829001220562306279887 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-531219199915502337744369350044368942839925154269120201256512402835869285787525175760085775388227 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P106 : ℚ := (277627478484067412193990476173622533310080851565 / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584)

theorem phaseChain2658P106 :
    phaseExp2646 phaseArg2658P106 20 =
      ((phaseValue2658P106.1,
        phaseValue2658P106.2), phaseRadius2658P106) := by
  decide +kernel

theorem phaseCosPin2658P106 :
    |Real.cos (phaseArg2658P106 : ℝ) -
      (phaseValue2658P106.1 : ℝ)| ≤
        (phaseRadius2658P106 : ℝ) := by
  have hsmall : |((phaseArg2658P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P106]
  have h := phaseExp_cos_error2646 phaseArg2658P106 20 hsmall
  rw [phaseChain2658P106] at h
  simpa [phaseValue2658P106] using h

theorem phaseSinPin2658P106 :
    |Real.sin (phaseArg2658P106 : ℝ) -
      (phaseValue2658P106.2 : ℝ)| ≤
        (phaseRadius2658P106 : ℝ) := by
  have hsmall : |((phaseArg2658P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P106]
  have h := phaseExp_sin_error2646 phaseArg2658P106 20 hsmall
  rw [phaseChain2658P106] at h
  simpa [phaseValue2658P106] using h

end ConnesWeilRH.Dev
