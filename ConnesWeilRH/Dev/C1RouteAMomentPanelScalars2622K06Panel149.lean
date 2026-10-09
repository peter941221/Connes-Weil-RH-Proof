import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P149 : ℚ := ((-18975053 : ℚ) / 430650)

def momentPanelGrowth2622K06P149 : ℚ := ((5881 : ℚ) / 6400)

theorem momentPanelPhase_owner2622K06P149 :
    (momentPanelPhase2622K06P149 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P149 :
    (momentPanelGrowth2622K06P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P149Input : RatPair2542 := (momentPanelPhase2622K06P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P149Expected : RatState2542 :=
  ((((39075500766177524808441957646199572147148369821993421521309929273295001966577 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((24768383970809425299860549269 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P149_replay :
    compactExp2620 momentScalarAmp2622K06P149Input 20 = momentScalarAmp2622K06P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K06P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P149_replay] at h
  simpa only [momentPanelPhase_owner2622K06P149] using h

theorem momentScalarAmp2622K06P149_radius_le :
    (momentScalarAmp2622K06P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P149Expected]

def momentScalarGrow2622K06P149Input : RatPair2542 := (momentPanelGrowth2622K06P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P149Expected : RatState2542 :=
  ((((167311020404541361915097542299011227319887244444918060168696120888927112696691885485803170385551 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((6786935346452527042496622657105100912820747201837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P149_replay :
    compactExp2620 momentScalarGrow2622K06P149Input 20 = momentScalarGrow2622K06P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P149] using h

theorem momentScalarGrow2622K06P149_radius_le :
    (momentScalarGrow2622K06P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P149Expected]

end ConnesWeilRH.Dev
