import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P160 : ℚ := ((-88064997873774207173343204052114867575 : ℚ) / 1632247195263471829037578994493423616)

def momentPanelGrowth2622K07P160 : ℚ := ((602866689251210061762707155541173054025 : ℚ) / 332519031256225542788563709635030155264)

theorem momentPanelPhase_owner2622K07P160 :
    (momentPanelPhase2622K07P160 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P160 :
    (momentPanelGrowth2622K07P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P160Input : RatPair2542 := (momentPanelPhase2622K07P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P160Expected : RatState2542 :=
  ((((3953496261807374461960840548436838285560347821322449931413058317020051343 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((12441671208173784116646483 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P160_replay :
    compactExp2620 momentScalarAmp2622K07P160Input 20 = momentScalarAmp2622K07P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K07P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P160_replay] at h
  simpa only [momentPanelPhase_owner2622K07P160] using h

theorem momentScalarAmp2622K07P160_radius_le :
    (momentScalarAmp2622K07P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P160Expected]

def momentScalarGrow2622K07P160Input : RatPair2542 := (momentPanelGrowth2622K07P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P160Expected : RatState2542 :=
  ((((13091432120932938251828977452088830294957251316718078290244434090244257302357998110988349316170785 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16595333091939607326133805254617915103928677531827 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P160_replay :
    compactExp2620 momentScalarGrow2622K07P160Input 20 = momentScalarGrow2622K07P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P160] using h

theorem momentScalarGrow2622K07P160_radius_le :
    (momentScalarGrow2622K07P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P160Expected]

end ConnesWeilRH.Dev
