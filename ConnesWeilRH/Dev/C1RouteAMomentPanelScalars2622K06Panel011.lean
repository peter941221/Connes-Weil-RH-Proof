import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P011 : ℚ := ((-20803369 : ℚ) / 255850)

def momentPanelGrowth2622K06P011 : ℚ := ((399710027 : ℚ) / 117750675)

theorem momentPanelPhase_owner2622K06P011 :
    (momentPanelPhase2622K06P011 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P011 :
    (momentPanelGrowth2622K06P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P011Input : RatPair2542 := (momentPanelPhase2622K06P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P011Expected : RatState2542 :=
  ((((2598396784304555963552887622467879270788691333228921715443795 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208925819621217409384207 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P011_replay :
    compactExp2620 momentScalarAmp2622K06P011Input 20 = momentScalarAmp2622K06P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K06P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P011_replay] at h
  simpa only [momentPanelPhase_owner2622K06P011] using h

theorem momentScalarAmp2622K06P011_radius_le :
    (momentScalarAmp2622K06P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P011Expected]

def momentScalarGrow2622K06P011Input : RatPair2542 := (momentPanelGrowth2622K06P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P011Expected : RatState2542 :=
  ((((7956847160537114769024231747187576511168261228633004916067475074786558065356042788025211211521717 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((10086469426090778469955140852539815197792687991119 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P011_replay :
    compactExp2620 momentScalarGrow2622K06P011Input 20 = momentScalarGrow2622K06P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P011] using h

theorem momentScalarGrow2622K06P011_radius_le :
    (momentScalarGrow2622K06P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P011Expected]

end ConnesWeilRH.Dev
