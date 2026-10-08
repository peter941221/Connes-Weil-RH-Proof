import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P001 : ℚ := ((-363283306592111837912693776724417904038434749157348209 : ℚ) / 2475132948690675625731279528219314465514959195340800)

def momentPanelGrowth2622K04P001 : ℚ := ((2559973982128595811592550987210379539626177809332239669 : ℚ) / 205630283152303358075508233562645176925803305028812800)

theorem momentPanelPhase_owner2622K04P001 :
    (momentPanelPhase2622K04P001 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-177 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P001, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P001 :
    (momentPanelGrowth2622K04P001 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P001, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P001Input : RatPair2542 := (momentPanelPhase2622K04P001 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P001Expected : RatState2542 :=
  ((((193088377462562142560785936898331 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P001_replay :
    compactExp2620 momentScalarAmp2622K04P001Input 20 = momentScalarAmp2622K04P001Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P001_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-177 / 200) 0) -
      (momentScalarAmp2622K04P001Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P001]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P001 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P001 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P001Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P001_replay] at h
  simpa only [momentPanelPhase_owner2622K04P001] using h

theorem momentScalarAmp2622K04P001_radius_le :
    (momentScalarAmp2622K04P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P001Expected]

def momentScalarGrow2622K04P001Input : RatPair2542 := (momentPanelGrowth2622K04P001 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P001Expected : RatState2542 :=
  ((((272442619586066961646979284427355534636522233664338409796851101134429560003901405390266505248965171159 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((690715899798264466976174004028642838240800773638210141 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P001_replay :
    compactExp2620 momentScalarGrow2622K04P001Input 20 = momentScalarGrow2622K04P001Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P001_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P001Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P001]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P001 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P001 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P001Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P001_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P001] using h

theorem momentScalarGrow2622K04P001_radius_le :
    (momentScalarGrow2622K04P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P001Expected]

end ConnesWeilRH.Dev
