import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P159 : ℚ := ((-797584371663752858929807600067613819697 : ℚ) / 13980664939797096423226840311450828800)

def momentPanelGrowth2622K05P159 : ℚ := ((1432176541799180780408358231888444163 : ℚ) / 879242456318299912878113343248793600)

theorem momentPanelPhase_owner2622K05P159 :
    (momentPanelPhase2622K05P159 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (139 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P159 :
    (momentPanelGrowth2622K05P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P159Input : RatPair2542 := (momentPanelPhase2622K05P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P159Expected : RatState2542 :=
  ((((178837539123317796393116792185617067704074536479975986210474101349416361 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1435641667855107367092709 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P159_replay :
    compactExp2620 momentScalarAmp2622K05P159Input 20 = momentScalarAmp2622K05P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K05P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P159_replay] at h
  simpa only [momentPanelPhase_owner2622K05P159] using h

theorem momentScalarAmp2622K05P159_radius_le :
    (momentScalarAmp2622K05P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P159Expected]

def momentScalarGrow2622K05P159Input : RatPair2542 := (momentPanelGrowth2622K05P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P159Expected : RatState2542 :=
  ((((10889558607723333378732317468072736504710386679147452444356501367368369800915400437822518909881499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1725516757713854893790782633115253916373582406631 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K05P159_replay :
    compactExp2620 momentScalarGrow2622K05P159Input 20 = momentScalarGrow2622K05P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P159] using h

theorem momentScalarGrow2622K05P159_radius_le :
    (momentScalarGrow2622K05P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P159Expected]

end ConnesWeilRH.Dev
