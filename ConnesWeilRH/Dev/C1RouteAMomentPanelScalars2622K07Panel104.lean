import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P104 : ℚ := ((-31212131078644023681647605454440487725 : ℚ) / 1058985170225861016175133884145467392)

def momentPanelGrowth2622K07P104 : ℚ := ((1084824976935877965527723693327512875 : ℚ) / 6201590125231742052166959447714824192)

theorem momentPanelPhase_owner2622K07P104 :
    (momentPanelPhase2622K07P104 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P104 :
    (momentPanelGrowth2622K07P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P104Input : RatPair2542 := (momentPanelPhase2622K07P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P104Expected : RatState2542 :=
  ((((84587504537362395300424165218242915755882389484055099559390227821104098977524127489 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((214460829829842190145469779483669857 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P104_replay :
    compactExp2620 momentScalarAmp2622K07P104Input 20 = momentScalarAmp2622K07P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K07P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P104_replay] at h
  simpa only [momentPanelPhase_owner2622K07P104] using h

theorem momentScalarAmp2622K07P104_radius_le :
    (momentScalarAmp2622K07P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P104Expected]

def momentScalarGrow2622K07P104Input : RatPair2542 := (momentPanelGrowth2622K07P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P104Expected : RatState2542 :=
  ((((636075124259409016685868613589568753554903159361343762177370470469227609810197089619690426477499 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1612641757089131862520835423113532582400084332145 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P104_replay :
    compactExp2620 momentScalarGrow2622K07P104Input 20 = momentScalarGrow2622K07P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P104] using h

theorem momentScalarGrow2622K07P104_radius_le :
    (momentScalarGrow2622K07P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P104Expected]

end ConnesWeilRH.Dev
