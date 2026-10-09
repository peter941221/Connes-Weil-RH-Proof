import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P111 : ℚ := ((-802707474773632203265035488983814904361 : ℚ) / 25793140292963829278133719460426547200)

def momentPanelGrowth2622K18P111 : ℚ := ((308514556036484844065861870576115790843 : ℚ) / 1913185949527012394164320753593981337600)

theorem momentPanelPhase_owner2622K18P111 :
    (momentPanelPhase2622K18P111 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (43 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P111 :
    (momentPanelGrowth2622K18P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P111Input : RatPair2542 := (momentPanelPhase2622K18P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P111Expected : RatState2542 :=
  ((((32576487928742729759526165172548221451263536887555051937413317085427244831274954615 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((82593660237748175288865580142718497 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K18P111_replay :
    compactExp2620 momentScalarAmp2622K18P111Input 20 = momentScalarAmp2622K18P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K18P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P111_replay] at h
  simpa only [momentPanelPhase_owner2622K18P111] using h

theorem momentScalarAmp2622K18P111_radius_le :
    (momentScalarAmp2622K18P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P111Expected]

def momentScalarGrow2622K18P111Input : RatPair2542 := (momentPanelGrowth2622K18P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P111Expected : RatState2542 :=
  ((((1254878348323458684095956139917487500631469418491673636634723550186709084648948086615379846646005 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3181494093660009444483020865954810971007787273245 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K18P111_replay :
    compactExp2620 momentScalarGrow2622K18P111Input 20 = momentScalarGrow2622K18P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P111] using h

theorem momentScalarGrow2622K18P111_radius_le :
    (momentScalarGrow2622K18P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P111Expected]

end ConnesWeilRH.Dev
