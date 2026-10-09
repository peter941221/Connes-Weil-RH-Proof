import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P053 : ℚ := ((-119102769684880913519099998833802881090173123954042819 : ℚ) / 3298940316920555669078122189785563058235080546713600)

def momentPanelGrowth2622K02P053 : ℚ := ((1201060096676611503532489102941988961447009012020410773 : ℚ) / 3544053980243876701303226846407059068613776154348748800)

theorem momentPanelPhase_owner2622K02P053 :
    (momentPanelPhase2622K02P053 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P053 :
    (momentPanelGrowth2622K02P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P053Input : RatPair2542 := (momentPanelPhase2622K02P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P053Expected : RatState2542 :=
  ((((446803442762040977141816985360938812778847764935331145929286957022649237643429493 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((70801269556881653226704168986207 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P053_replay :
    compactExp2620 momentScalarAmp2622K02P053Input 20 = momentScalarAmp2622K02P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K02P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P053_replay] at h
  simpa only [momentPanelPhase_owner2622K02P053] using h

theorem momentScalarAmp2622K02P053_radius_le :
    (momentScalarAmp2622K02P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P053Expected]

def momentScalarGrow2622K02P053Input : RatPair2542 := (momentPanelGrowth2622K02P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P053Expected : RatState2542 :=
  ((((2997633864727658309814796053529973334595656180014813385208082800974996293338482572331422922411819 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3799951139761461510423881606343925188755009186119 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P053_replay :
    compactExp2620 momentScalarGrow2622K02P053Input 20 = momentScalarGrow2622K02P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P053] using h

theorem momentScalarGrow2622K02P053_radius_le :
    (momentScalarGrow2622K02P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P053Expected]

end ConnesWeilRH.Dev
