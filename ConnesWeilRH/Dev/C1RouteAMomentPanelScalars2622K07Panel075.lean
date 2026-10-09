import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P075 : ℚ := ((-33691579653041321674983598660810712275 : ℚ) / 1058985170225861016175133884145467392)

def momentPanelGrowth2622K07P075 : ℚ := ((1084824976935877965527723693327512875 : ℚ) / 6201590125231742052166959447714824192)

theorem momentPanelPhase_owner2622K07P075 :
    (momentPanelPhase2622K07P075 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P075 :
    (momentPanelGrowth2622K07P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P075Input : RatPair2542 := (momentPanelPhase2622K07P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P075Expected : RatState2542 :=
  ((((32548683303118094306866665715763504869431641100987906172647416507196891056463716829 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5157701229080221684614749309672449 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P075_replay :
    compactExp2620 momentScalarAmp2622K07P075Input 20 = momentScalarAmp2622K07P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K07P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P075_replay] at h
  simpa only [momentPanelPhase_owner2622K07P075] using h

theorem momentScalarAmp2622K07P075_radius_le :
    (momentScalarAmp2622K07P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P075Expected]

def momentScalarGrow2622K07P075Input : RatPair2542 := (momentPanelGrowth2622K07P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P075Expected : RatState2542 :=
  ((((636075124259409016685868613589568753554903159361343762177370470469227609810197089619690426477499 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1612641757089131862520835423113532582400084332145 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P075_replay :
    compactExp2620 momentScalarGrow2622K07P075Input 20 = momentScalarGrow2622K07P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P075] using h

theorem momentScalarGrow2622K07P075_radius_le :
    (momentScalarGrow2622K07P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P075Expected]

end ConnesWeilRH.Dev
