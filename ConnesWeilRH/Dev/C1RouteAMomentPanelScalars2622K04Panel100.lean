import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P100 : ℚ := ((-331311205221822364007621690540256065524750049650658547 : ℚ) / 11292098295151013386956946933090515620033014739763200)

def momentPanelGrowth2622K04P100 : ℚ := ((753689812726917360394229272040232805358713586439491269 : ℚ) / 4643057539590549105076203975458681515550673178774732800)

theorem momentPanelPhase_owner2622K04P100 :
    (momentPanelPhase2622K04P100 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P100 :
    (momentPanelGrowth2622K04P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P100Input : RatPair2542 := (momentPanelPhase2622K04P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P100Expected : RatState2542 :=
  ((((193343008252932106042338880719195920441515974726971242997940452400806143888088310419 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((61274559608613946911222766410237717 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P100_replay :
    compactExp2620 momentScalarAmp2622K04P100Input 20 = momentScalarAmp2622K04P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K04P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P100_replay] at h
  simpa only [momentPanelPhase_owner2622K04P100] using h

theorem momentScalarAmp2622K04P100_radius_le :
    (momentScalarAmp2622K04P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P100Expected]

def momentScalarGrow2622K04P100Input : RatPair2542 := (momentPanelGrowth2622K04P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P100Expected : RatState2542 :=
  ((((1256220808128105618822000181308388973010879425725968718642832155720448293202636012793281366747715 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3184897629843272759434305272591786237882641268029 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P100_replay :
    compactExp2620 momentScalarGrow2622K04P100Input 20 = momentScalarGrow2622K04P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P100] using h

theorem momentScalarGrow2622K04P100_radius_le :
    (momentScalarGrow2622K04P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P100Expected]

end ConnesWeilRH.Dev
