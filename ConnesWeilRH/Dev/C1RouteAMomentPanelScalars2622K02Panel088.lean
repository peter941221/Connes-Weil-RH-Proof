import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P088 : ℚ := ((-343239516055244848895532718208240056793717636864282667 : ℚ) / 11415412495800808320680382840850951999816484048076800)

def momentPanelGrowth2622K02P088 : ℚ := ((15715120744275262970270529794862501639283890208910893 : ℚ) / 297105442273213738772295897916602219206846301654220800)

theorem momentPanelPhase_owner2622K02P088 :
    (momentPanelPhase2622K02P088 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P088 :
    (momentPanelGrowth2622K02P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P088Input : RatPair2542 := (momentPanelPhase2622K02P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P088Expected : RatState2542 :=
  ((((93361572105521254712059471294704892609176236521046709119309327224337833291516104697 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((236706493335871138185713073026359029 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P088_replay :
    compactExp2620 momentScalarAmp2622K02P088Input 20 = momentScalarAmp2622K02P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K02P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P088_replay] at h
  simpa only [momentPanelPhase_owner2622K02P088] using h

theorem momentScalarAmp2622K02P088_radius_le :
    (momentScalarAmp2622K02P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P088Expected]

def momentScalarGrow2622K02P088Input : RatPair2542 := (momentPanelGrowth2622K02P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P088Expected : RatState2542 :=
  ((((1126004759882011125937543198533075322306963257826720967328738319159144015822779076878004473834955 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1427380537721872939557543896841183045858187276529 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P088_replay :
    compactExp2620 momentScalarGrow2622K02P088Input 20 = momentScalarGrow2622K02P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P088] using h

theorem momentScalarGrow2622K02P088_radius_le :
    (momentScalarGrow2622K02P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P088Expected]

end ConnesWeilRH.Dev
