import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P172 : ℚ := ((-3618087541453660921816689605330358375 : ℚ) / 41457245229864014346548181628616704)

def momentPanelGrowth2622K07P172 : ℚ := ((683941632322246751340155193366370300025 : ℚ) / 130866447198415759032778390009150439424)

theorem momentPanelPhase_owner2622K07P172 :
    (momentPanelPhase2622K07P172 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P172 :
    (momentPanelGrowth2622K07P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P172Input : RatPair2542 := (momentPanelPhase2622K07P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P172Expected : RatState2542 :=
  ((((26762554277846640220440220814351656660623729341575440514307 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807323069586341 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P172_replay :
    compactExp2620 momentScalarAmp2622K07P172Input 20 = momentScalarAmp2622K07P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K07P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P172_replay] at h
  simpa only [momentPanelPhase_owner2622K07P172] using h

theorem momentScalarAmp2622K07P172_radius_le :
    (momentScalarAmp2622K07P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P172Expected]

def momentScalarGrow2622K07P172Input : RatPair2542 := (momentPanelGrowth2622K07P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P172Expected : RatState2542 :=
  ((((24843514221663097166423955749166712904174418292284197106877838687170553846605969176985472609232411 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((125970955000196979008479380577960503990501164388617 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P172_replay :
    compactExp2620 momentScalarGrow2622K07P172Input 20 = momentScalarGrow2622K07P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P172] using h

theorem momentScalarGrow2622K07P172_radius_le :
    (momentScalarGrow2622K07P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P172Expected]

end ConnesWeilRH.Dev
