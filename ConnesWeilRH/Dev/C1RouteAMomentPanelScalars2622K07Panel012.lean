import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P012 : ℚ := ((-1406199701288547508249539754628090125 : ℚ) / 17280612982311223201203058095685632)

def momentPanelGrowth2622K07P012 : ℚ := ((121791029985843631379609753323117629075 : ℚ) / 38878985885867021305596854939640922112)

theorem momentPanelPhase_owner2622K07P012 :
    (momentPanelPhase2622K07P012 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P012, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P012 :
    (momentPanelGrowth2622K07P012 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P012, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P012Input : RatPair2542 := (momentPanelPhase2622K07P012 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P012Expected : RatState2542 :=
  ((((4876531100129587437939681827910964627760333452319677042561273 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639241622794398513 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P012_replay :
    compactExp2620 momentScalarAmp2622K07P012Input 20 = momentScalarAmp2622K07P012Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P012_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 40) 0) -
      (momentScalarAmp2622K07P012Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P012]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P012 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P012 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P012Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P012_replay] at h
  simpa only [momentPanelPhase_owner2622K07P012] using h

theorem momentScalarAmp2622K07P012_radius_le :
    (momentScalarAmp2622K07P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P012Expected]

def momentScalarGrow2622K07P012Input : RatPair2542 := (momentPanelGrowth2622K07P012 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P012Expected : RatState2542 :=
  ((((765376671610126888151874105658444057366029179937503480344974943483859583404462063140360107040837 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((62094547114151334521315043542612580359109147158431 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P012_replay :
    compactExp2620 momentScalarGrow2622K07P012Input 20 = momentScalarGrow2622K07P012Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P012_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P012Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P012]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P012 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P012 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P012Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P012_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P012] using h

theorem momentScalarGrow2622K07P012_radius_le :
    (momentScalarGrow2622K07P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P012Expected]

end ConnesWeilRH.Dev
