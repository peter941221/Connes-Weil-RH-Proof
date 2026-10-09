import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P157 : ℚ := ((-19101738802708558797505515685772977227 : ℚ) / 353319575295612098785161117402398720)

def momentPanelGrowth2622K09P157 : ℚ := ((212758691284083621814456990243709243 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K09P157 :
    (momentPanelPhase2622K09P157 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (27 / 40) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P157, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P157 :
    (momentPanelGrowth2622K09P157 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P157, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P157Input : RatPair2542 := (momentPanelPhase2622K09P157 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P157Expected : RatState2542 :=
  ((((3540237688756237629927259181094768436171767098370184991755927159546614623 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5696941642792294847338103 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K09P157_replay :
    compactExp2620 momentScalarAmp2622K09P157Input 20 = momentScalarAmp2622K09P157Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P157_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (27 / 40) 0) -
      (momentScalarAmp2622K09P157Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P157]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P157 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P157 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P157Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P157_replay] at h
  simpa only [momentPanelPhase_owner2622K09P157] using h

theorem momentScalarAmp2622K09P157_radius_le :
    (momentScalarAmp2622K09P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P157Expected]

def momentScalarGrow2622K09P157Input : RatPair2542 := (momentPanelGrowth2622K09P157 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P157Expected : RatState2542 :=
  ((((2225140327415508536393544672627651493900455633077028150108294093771090285148032536761056246280139 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2820696632471712667818850741536272652426046634289 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K09P157_replay :
    compactExp2620 momentScalarGrow2622K09P157Input 20 = momentScalarGrow2622K09P157Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P157_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P157Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P157]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P157 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P157 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P157Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P157_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P157] using h

theorem momentScalarGrow2622K09P157_radius_le :
    (momentScalarGrow2622K09P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P157Expected]

end ConnesWeilRH.Dev
