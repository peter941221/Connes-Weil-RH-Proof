import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P146 : ℚ := ((-28476805013358130483896927930964977404050378494467627 : ℚ) / 647756365334599892018303087234653367647309555302400)

def momentPanelGrowth2622K01P146 : ℚ := ((1223324903037749410360520884958926779713018442762564273 : ℚ) / 1626206056750363006126808060047903994631879912954265600)

theorem momentPanelPhase_owner2622K01P146 :
    (momentPanelPhase2622K01P146 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P146 :
    (momentPanelGrowth2622K01P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P146Input : RatPair2542 := (momentPanelPhase2622K01P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P146Expected : RatState2542 :=
  ((((86302018455372258540628921302107933259098526927032618826226103626473052621381 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((218813202432351068347294418593 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P146_replay :
    compactExp2620 momentScalarAmp2622K01P146Input 20 = momentScalarAmp2622K01P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K01P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P146_replay] at h
  simpa only [momentPanelPhase_owner2622K01P146] using h

theorem momentScalarAmp2622K01P146_radius_le :
    (momentScalarAmp2622K01P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P146Expected]

def momentScalarGrow2622K01P146Input : RatPair2542 := (momentPanelGrowth2622K01P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P146Expected : RatState2542 :=
  ((((2266051023714395577371132776753694601173921826126005934521725345826689243510064871874129641331125 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2872558879561347097476709930275072232075194057469 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P146_replay :
    compactExp2620 momentScalarGrow2622K01P146Input 20 = momentScalarGrow2622K01P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P146] using h

theorem momentScalarGrow2622K01P146_radius_le :
    (momentScalarGrow2622K01P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P146Expected]

end ConnesWeilRH.Dev
