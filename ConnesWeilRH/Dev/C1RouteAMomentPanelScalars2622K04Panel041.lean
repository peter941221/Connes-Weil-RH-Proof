import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P041 : ℚ := ((-127548580160369070294890349434504891256741092302662443 : ℚ) / 2910728944504534581430268406095300381138973464985600)

def momentPanelGrowth2622K04P041 : ℚ := ((1658861683164980308115459755062715432624059113255362709 : ℚ) / 2747204466433826828189813090231772540029652121210060800)

theorem momentPanelPhase_owner2622K04P041 :
    (momentPanelPhase2622K04P041 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-97 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P041 :
    (momentPanelGrowth2622K04P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P041Input : RatPair2542 := (momentPanelPhase2622K04P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P041Expected : RatState2542 :=
  ((((198952358469345025016248378290887809625874850354870971931724887503140054694879 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((63053758566367613590719869695 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P041_replay :
    compactExp2620 momentScalarAmp2622K04P041Input 20 = momentScalarAmp2622K04P041Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622K04P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P041]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P041 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P041_replay] at h
  simpa only [momentPanelPhase_owner2622K04P041] using h

theorem momentScalarAmp2622K04P041_radius_le :
    (momentScalarAmp2622K04P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P041Expected]

def momentScalarGrow2622K04P041Input : RatPair2542 := (momentPanelGrowth2622K04P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P041Expected : RatState2542 :=
  ((((3906981638328671544558836333302646479264493168195704591753259927576353490401352769784979018249541 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2476342383419302309870473153944268462836851555893 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P041_replay :
    compactExp2620 momentScalarGrow2622K04P041Input 20 = momentScalarGrow2622K04P041Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P041_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P041] using h

theorem momentScalarGrow2622K04P041_radius_le :
    (momentScalarGrow2622K04P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P041Expected]

end ConnesWeilRH.Dev
