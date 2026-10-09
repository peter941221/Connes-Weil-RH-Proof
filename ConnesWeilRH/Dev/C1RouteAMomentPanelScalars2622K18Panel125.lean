import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P125 : ℚ := ((-798301243371118763009300396944157208053 : ℚ) / 23635091911135291545025731923594444800)

def momentPanelGrowth2622K18P125 : ℚ := ((88100188372915779430412633795591641 : ℚ) / 293080818772766637626037781082931200)

theorem momentPanelPhase_owner2622K18P125 :
    (momentPanelPhase2622K18P125 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (71 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P125 :
    (momentPanelGrowth2622K18P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P125Input : RatPair2542 := (momentPanelPhase2622K18P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P125Expected : RatState2542 :=
  ((((2289783820334702804429583634276886635045842125228193907729280964912294080590405791 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2902739335240133586860786431465619 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K18P125_replay :
    compactExp2620 momentScalarAmp2622K18P125Input 20 = momentScalarAmp2622K18P125Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622K18P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P125]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P125 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P125_replay] at h
  simpa only [momentPanelPhase_owner2622K18P125] using h

theorem momentScalarAmp2622K18P125_radius_le :
    (momentScalarAmp2622K18P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P125Expected]

def momentScalarGrow2622K18P125Input : RatPair2542 := (momentPanelGrowth2622K18P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P125Expected : RatState2542 :=
  ((((721253082179815747316439612563880155510868387098283818129801182743386559482388858917460343688947 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((914296640435854143092315788293698241478807593075 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K18P125_replay :
    compactExp2620 momentScalarGrow2622K18P125Input 20 = momentScalarGrow2622K18P125Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P125_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P125] using h

theorem momentScalarGrow2622K18P125_radius_le :
    (momentScalarGrow2622K18P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P125Expected]

end ConnesWeilRH.Dev
