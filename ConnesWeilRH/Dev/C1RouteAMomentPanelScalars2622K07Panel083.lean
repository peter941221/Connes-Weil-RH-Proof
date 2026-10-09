import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P083 : ℚ := ((-33017130759515613541359090228415651075 : ℚ) / 1077158209230732912874990621297737728)

def momentPanelGrowth2622K07P083 : ℚ := ((164891562659377835800614538826845662025 : ℚ) / 1338941931346031182026629813127761362944)

theorem momentPanelPhase_owner2622K07P083 :
    (momentPanelPhase2622K07P083 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P083 :
    (momentPanelGrowth2622K07P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P083Input : RatPair2542 := (momentPanelPhase2622K07P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P083Expected : RatState2542 :=
  ((((104129306205610756724311949035167980593137088587842187703307592283437559012796726743 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((66001718097857177823966202042537835 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P083_replay :
    compactExp2620 momentScalarAmp2622K07P083Input 20 = momentScalarAmp2622K07P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K07P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P083_replay] at h
  simpa only [momentPanelPhase_owner2622K07P083] using h

theorem momentScalarAmp2622K07P083_radius_le :
    (momentScalarAmp2622K07P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P083Expected]

def momentScalarGrow2622K07P083Input : RatPair2542 := (momentPanelGrowth2622K07P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P083Expected : RatState2542 :=
  ((((2415918381235980352545827903269420232362909118157404681602346705491880799126212466730985404374315 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((382817503299288552423866235421858970382195779195 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P083_replay :
    compactExp2620 momentScalarGrow2622K07P083Input 20 = momentScalarGrow2622K07P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P083] using h

theorem momentScalarGrow2622K07P083_radius_le :
    (momentScalarGrow2622K07P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P083Expected]

end ConnesWeilRH.Dev
