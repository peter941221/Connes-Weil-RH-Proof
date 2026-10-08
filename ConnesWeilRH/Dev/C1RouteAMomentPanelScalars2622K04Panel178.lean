import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P178 : ℚ := ((-321795585906748904995283488611339761425283630362651791 : ℚ) / 2475132948690675625731279528219314465514959195340800)

def momentPanelGrowth2622K04P178 : ℚ := ((2559973982128595811592550987210379539626177809332239669 : ℚ) / 205630283152303358075508233562645176925803305028812800)

theorem momentPanelPhase_owner2622K04P178 :
    (momentPanelPhase2622K04P178 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (177 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P178, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P178 :
    (momentPanelGrowth2622K04P178 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P178, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P178Input : RatPair2542 := (momentPanelPhase2622K04P178 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P178Expected : RatState2542 :=
  ((((3675529490968559488938696722710163060925 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P178_replay :
    compactExp2620 momentScalarAmp2622K04P178Input 20 = momentScalarAmp2622K04P178Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P178_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (177 / 200) 0) -
      (momentScalarAmp2622K04P178Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P178]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P178 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P178 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P178Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P178_replay] at h
  simpa only [momentPanelPhase_owner2622K04P178] using h

theorem momentScalarAmp2622K04P178_radius_le :
    (momentScalarAmp2622K04P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P178Expected]

def momentScalarGrow2622K04P178Input : RatPair2542 := (momentPanelGrowth2622K04P178 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P178Expected : RatState2542 :=
  ((((272442619586066961646979284427355534636522233664338409796851101134429560003901405390266505248965171159 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((690715899798264466976174004028642838240800773638210141 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P178_replay :
    compactExp2620 momentScalarGrow2622K04P178Input 20 = momentScalarGrow2622K04P178Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P178_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P178Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P178]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P178 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P178 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P178Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P178_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P178] using h

theorem momentScalarGrow2622K04P178_radius_le :
    (momentScalarGrow2622K04P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P178Expected]

end ConnesWeilRH.Dev
