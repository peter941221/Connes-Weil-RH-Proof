import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P054 : ℚ := ((-28599924873293985195607120057494541302164886744578099 : ℚ) / 831585868155127524698610320099748341213407320473600)

def momentPanelGrowth2622K01P054 : ℚ := ((2959241166993663326678707603840981186326507402897 : ℚ) / 10311864579800560140646116129272602360365344358400)

theorem momentPanelPhase_owner2622K01P054 :
    (momentPanelPhase2622K01P054 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P054 :
    (momentPanelGrowth2622K01P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P054Input : RatPair2542 := (momentPanelPhase2622K01P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P054Expected : RatState2542 :=
  ((((2473605374293779569760477485850222435614882193745905264246913976464708500010140099 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((391971273457956359774664063654729 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P054_replay :
    compactExp2620 momentScalarAmp2622K01P054Input 20 = momentScalarAmp2622K01P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K01P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P054_replay] at h
  simpa only [momentPanelPhase_owner2622K01P054] using h

theorem momentScalarAmp2622K01P054_radius_le :
    (momentScalarAmp2622K01P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P054Expected]

def momentScalarGrow2622K01P054Input : RatPair2542 := (momentPanelGrowth2622K01P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P054Expected : RatState2542 :=
  ((((711491998280842688131447984301597388031963788413443599752356704116013880210546944599190211844265 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((901923011839864100441380762710704668044371803957 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P054_replay :
    compactExp2620 momentScalarGrow2622K01P054Input 20 = momentScalarGrow2622K01P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P054] using h

theorem momentScalarGrow2622K01P054_radius_le :
    (momentScalarGrow2622K01P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P054Expected]

end ConnesWeilRH.Dev
