import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P011 : ℚ := ((-822793613381756952135233525611701528841 : ℚ) / 10378508994188559755933808483054387200)

def momentPanelGrowth2622K05P011 : ℚ := ((16090510046588006962682951686151517999403 : ℚ) / 4776534842912933314594650006646004121600)

theorem momentPanelPhase_owner2622K05P011 :
    (momentPanelPhase2622K05P011 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P011 :
    (momentPanelGrowth2622K05P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P011Input : RatPair2542 := (momentPanelPhase2622K05P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P011Expected : RatState2542 :=
  ((((79312599066309188426125804044727781290640301761348202190859279 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231454916225830556487 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P011_replay :
    compactExp2620 momentScalarAmp2622K05P011Input 20 = momentScalarAmp2622K05P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K05P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P011_replay] at h
  simpa only [momentPanelPhase_owner2622K05P011] using h

theorem momentScalarAmp2622K05P011_radius_le :
    (momentScalarAmp2622K05P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P011Expected]

def momentScalarGrow2622K05P011Input : RatPair2542 := (momentPanelGrowth2622K05P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P011Expected : RatState2542 :=
  ((((62028029879641659313416107423549416012049321903830758150850414941886506699036981274020166617076989 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((39314808350909911873069808897824235936625376743881 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P011_replay :
    compactExp2620 momentScalarGrow2622K05P011Input 20 = momentScalarGrow2622K05P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P011] using h

theorem momentScalarGrow2622K05P011_radius_le :
    (momentScalarGrow2622K05P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P011Expected]

end ConnesWeilRH.Dev
