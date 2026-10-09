import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K26
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K26P100 : ℚ := ((-2420840985850814295837492054761323722309 : ℚ) / 80235184151085643030092931362350694400)

def momentPanelGrowth2622K26P100 : ℚ := ((2742028240508102621525968156901888795843 : ℚ) / 32990908064722284401257496536591997337600)

theorem momentPanelPhase_owner2622K26P100 :
    (momentPanelPhase2622K26P100 : ℝ) = momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K26P100 :
    (momentPanelGrowth2622K26P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K26P100Input : RatPair2542 := (momentPanelPhase2622K26P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K26P100Expected : RatState2542 :=
  ((((84162116424931135437724517535849731706154045278617513392098882822823855816923903973 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((106691227301845711552532400858062523 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K26P100_replay :
    compactExp2620 momentScalarAmp2622K26P100Input 20 = momentScalarAmp2622K26P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K26P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K26P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K26P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K26P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K26P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K26P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K26P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K26P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K26P100_replay] at h
  simpa only [momentPanelPhase_owner2622K26P100] using h

theorem momentScalarAmp2622K26P100_radius_le :
    (momentScalarAmp2622K26P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarAmp2622K26P100Expected]

def momentScalarGrow2622K26P100Input : RatPair2542 := (momentPanelGrowth2622K26P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K26P100Expected : RatState2542 :=
  ((((2321105349127021486083433022243735956943947077584315107481654124215691067765804189396016826264437 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2942350355790412166419553207239883106755002487651 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K26P100_replay :
    compactExp2620 momentScalarGrow2622K26P100Input 20 = momentScalarGrow2622K26P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K26P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K26P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K26P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K26P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K26P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K26P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K26P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K26P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K26P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K26P100] using h

theorem momentScalarGrow2622K26P100_radius_le :
    (momentScalarGrow2622K26P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarGrow2622K26P100Expected]

end ConnesWeilRH.Dev
