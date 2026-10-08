import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P045 : ℚ := ((-127042650478308371405428788850830385278212927220039779 : ℚ) / 3052311915620965801631250374264690298668141930086400)

def momentPanelGrowth2622K04P045 : ℚ := ((7541108364830492029474260299202130030020991782766047 : ℚ) / 14523815245745118345637223853715007457344467920486400)

theorem momentPanelPhase_owner2622K04P045 :
    (momentPanelPhase2622K04P045 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P045 :
    (momentPanelGrowth2622K04P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P045Input : RatPair2542 := (momentPanelPhase2622K04P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P045Expected : RatState2542 :=
  ((((448156695997445709348428145908795584050066244442099776656969117144303737884125 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1136258519552855381593158449217 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P045_replay :
    compactExp2620 momentScalarAmp2622K04P045Input 20 = momentScalarAmp2622K04P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K04P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P045_replay] at h
  simpa only [momentPanelPhase_owner2622K04P045] using h

theorem momentScalarAmp2622K04P045_radius_le :
    (momentScalarAmp2622K04P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P045Expected]

def momentScalarGrow2622K04P045Input : RatPair2542 := (momentPanelGrowth2622K04P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P045Expected : RatState2542 :=
  ((((112187533580349232683901267132837792695092064116992063218637327837629048701580736977089323007677 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((71107261930417111737556404254304887605529111631 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K04P045_replay :
    compactExp2620 momentScalarGrow2622K04P045Input 20 = momentScalarGrow2622K04P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P045] using h

theorem momentScalarGrow2622K04P045_radius_le :
    (momentScalarGrow2622K04P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P045Expected]

end ConnesWeilRH.Dev
