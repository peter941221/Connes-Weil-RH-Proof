import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K17
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K17P129 : ℚ := ((-797333333813747453346518898534521708797 : ℚ) / 22823795526989224728067841872153804800)

def momentPanelGrowth2622K17P129 : ℚ := ((53014908614698151141474000378749243 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K17P129 :
    (momentPanelPhase2622K17P129 : ℝ) = momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K17P129 :
    (momentPanelGrowth2622K17P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K17P129Input : RatPair2542 := (momentPanelPhase2622K17P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K17P129Expected : RatState2542 :=
  ((((179777213616185773313236778530190228830429330316034344519973755211427869419332977 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((227902285703730839634564274723319 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K17P129_replay :
    compactExp2620 momentScalarAmp2622K17P129Input 20 = momentScalarAmp2622K17P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K17P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K17P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K17P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K17P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelPhase2622K17P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K17P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K17P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K17P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K17P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K17P129_replay] at h
  simpa only [momentPanelPhase_owner2622K17P129] using h

theorem momentScalarAmp2622K17P129_radius_le :
    (momentScalarAmp2622K17P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarAmp2622K17P129Expected]

def momentScalarGrow2622K17P129Input : RatPair2542 := (momentPanelGrowth2622K17P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K17P129Expected : RatState2542 :=
  ((((1524102520415809924686331722086637448904441999079668312376051406149652359306682736747432799662051 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1932028819567687325975472863822562004774266584721 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K17P129_replay :
    compactExp2620 momentScalarGrow2622K17P129Input 20 = momentScalarGrow2622K17P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K17P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 17).re * (storedWidth 17 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K17P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K17P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K17P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentPanelGrowth2622K17P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K17P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K17P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K17P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K17P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K17P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K17P129] using h

theorem momentScalarGrow2622K17P129_radius_le :
    (momentScalarGrow2622K17P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, momentScalarGrow2622K17P129Expected]

end ConnesWeilRH.Dev
