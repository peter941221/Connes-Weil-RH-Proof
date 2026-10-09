import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P024 : ℚ := ((-20997303 : ℚ) / 380650)

def momentPanelGrowth2622K06P024 : ℚ := ((63865921 : ℚ) / 49773025)

theorem momentPanelPhase_owner2622K06P024 :
    (momentPanelPhase2622K06P024 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P024 :
    (momentPanelGrowth2622K06P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P024Input : RatPair2542 := (momentPanelPhase2622K06P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P024Expected : RatState2542 :=
  ((((590356754701607250684826897412370394341239922139941764376167025635647539 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1352868374062646076760799 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P024_replay :
    compactExp2620 momentScalarAmp2622K06P024Input 20 = momentScalarAmp2622K06P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K06P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P024_replay] at h
  simpa only [momentPanelPhase_owner2622K06P024] using h

theorem momentScalarAmp2622K06P024_radius_le :
    (momentScalarAmp2622K06P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P024Expected]

def momentScalarGrow2622K06P024Input : RatPair2542 := (momentPanelGrowth2622K06P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P024Expected : RatState2542 :=
  ((((7706561435902640467723540313542391489329980984385879868110363644752438606233988024282128763876831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1221151909414278779389388967618883647954674412139 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P024_replay :
    compactExp2620 momentScalarGrow2622K06P024Input 20 = momentScalarGrow2622K06P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P024] using h

theorem momentScalarGrow2622K06P024_radius_le :
    (momentScalarGrow2622K06P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P024Expected]

end ConnesWeilRH.Dev
