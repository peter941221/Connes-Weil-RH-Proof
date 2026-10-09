import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P166 : ℚ := ((-2394018908988389468332342107822468926913 : ℚ) / 33650545773418486400370884608629145600)

def momentPanelGrowth2622K13P166 : ℚ := ((15704224644771794054909751892068855139043 : ℚ) / 5602353432335214727576086290007431577600)

theorem momentPanelPhase_owner2622K13P166 :
    (momentPanelPhase2622K13P166 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (153 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P166 :
    (momentPanelGrowth2622K13P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P166Input : RatPair2542 := (momentPanelPhase2622K13P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P166Expected : RatState2542 :=
  ((((8456726957563213701440664555232866464473286771343187626685901325 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((604462995574533964204605 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K13P166_replay :
    compactExp2620 momentScalarAmp2622K13P166Input 20 = momentScalarAmp2622K13P166Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622K13P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P166]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P166 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P166_replay] at h
  simpa only [momentPanelPhase_owner2622K13P166] using h

theorem momentScalarAmp2622K13P166_radius_le :
    (momentScalarAmp2622K13P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P166Expected]

def momentScalarGrow2622K13P166Input : RatPair2542 := (momentPanelGrowth2622K13P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P166Expected : RatState2542 :=
  ((((35236294393972079532401075861097599347624031560586348633083000139443183129679580397150938445724137 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5583398791227762670129265049017302598948118465591 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K13P166_replay :
    compactExp2620 momentScalarGrow2622K13P166Input 20 = momentScalarGrow2622K13P166Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P166_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P166] using h

theorem momentScalarGrow2622K13P166_radius_le :
    (momentScalarGrow2622K13P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P166Expected]

end ConnesWeilRH.Dev
