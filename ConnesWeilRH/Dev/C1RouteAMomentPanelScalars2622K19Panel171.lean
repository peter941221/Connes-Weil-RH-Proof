import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P171 : ℚ := ((-799834405576008550734917488057381606881 : ℚ) / 9080434779554852848801184400749363200)

def momentPanelGrowth2622K19P171 : ℚ := ((1042985305672218520326419159969321758603 : ℚ) / 226744155802583301753954703664322969600)

theorem momentPanelPhase_owner2622K19P171 :
    (momentPanelPhase2622K19P171 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (163 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P171 :
    (momentPanelGrowth2622K19P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P171Input : RatPair2542 := (momentPanelPhase2622K19P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P171Expected : RatState2542 :=
  ((((371851642300183565651198166787387403045747706971114384207 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((2417851639229273435135081 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K19P171_replay :
    compactExp2620 momentScalarAmp2622K19P171Input 20 = momentScalarAmp2622K19P171Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622K19P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P171]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P171 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P171_replay] at h
  simpa only [momentPanelPhase_owner2622K19P171] using h

theorem momentScalarAmp2622K19P171_radius_le :
    (momentScalarAmp2622K19P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P171Expected]

def momentScalarGrow2622K19P171Input : RatPair2542 := (momentPanelGrowth2622K19P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P171Expected : RatState2542 :=
  ((((212461776191752688650118771605211850084131444537108142847770932079173403830737391546402478025406283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((134663058324015027825381086334668559768966043401045 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K19P171_replay :
    compactExp2620 momentScalarGrow2622K19P171Input 20 = momentScalarGrow2622K19P171Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P171_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P171] using h

theorem momentScalarGrow2622K19P171_radius_le :
    (momentScalarGrow2622K19P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P171Expected]

end ConnesWeilRH.Dev
