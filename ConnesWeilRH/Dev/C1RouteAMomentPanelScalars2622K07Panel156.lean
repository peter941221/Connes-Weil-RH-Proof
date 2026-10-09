import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P156 : ℚ := ((-29212443296010093843926241260295189925 : ℚ) / 603361120889429891771582831256403968)

def momentPanelGrowth2622K07P156 : ℚ := ((576724135340185420925667207108170820025 : ℚ) / 410666344162711282865215510949998362624)

theorem momentPanelPhase_owner2622K07P156 :
    (momentPanelPhase2622K07P156 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P156 :
    (momentPanelGrowth2622K07P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P156Input : RatPair2542 := (momentPanelPhase2622K07P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P156Expected : RatState2542 :=
  ((((2007783530806349557840771512085565485754876124152671040962280145835297368085 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((636925842760180115823253493 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P156_replay :
    compactExp2620 momentScalarAmp2622K07P156Input 20 = momentScalarAmp2622K07P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K07P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P156_replay] at h
  simpa only [momentPanelPhase_owner2622K07P156] using h

theorem momentScalarAmp2622K07P156_radius_le :
    (momentScalarAmp2622K07P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P156Expected]

def momentScalarGrow2622K07P156Input : RatPair2542 := (momentPanelGrowth2622K07P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P156Expected : RatState2542 :=
  ((((4349859271671612291357822090236713476498093772880727533742899579908512451271566838835603299112381 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5514094331590407493225441428506590697783298255057 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P156_replay :
    compactExp2620 momentScalarGrow2622K07P156Input 20 = momentScalarGrow2622K07P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P156] using h

theorem momentScalarGrow2622K07P156_radius_le :
    (momentScalarGrow2622K07P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P156Expected]

end ConnesWeilRH.Dev
