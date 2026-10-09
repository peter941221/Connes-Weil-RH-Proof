import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P004 : ℚ := ((-219722737484359180108870849444385813973298698554942325 : ℚ) / 1965537014505398062119180639399311126059772278734848)

def momentPanelGrowth2622K03P004 : ℚ := ((98232840848492228347428458925316741026212578418334475 : ℚ) / 12903871987551541409117496578958197083608413909286912)

theorem momentPanelPhase_owner2622K03P004 :
    (momentPanelPhase2622K03P004 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P004 :
    (momentPanelGrowth2622K03P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P004Input : RatPair2542 := (momentPanelPhase2622K03P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P004Expected : RatState2542 :=
  ((((603732973368601702018391654068057273895808753247 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807314587353089 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P004_replay :
    compactExp2620 momentScalarAmp2622K03P004Input 20 = momentScalarAmp2622K03P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K03P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P004_replay] at h
  simpa only [momentPanelPhase_owner2622K03P004] using h

theorem momentScalarAmp2622K03P004_radius_le :
    (momentScalarAmp2622K03P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P004Expected]

def momentScalarGrow2622K03P004Input : RatPair2542 := (momentPanelGrowth2622K03P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P004Expected : RatState2542 :=
  ((((2161257705063451223013678530249870628525017089048535273027075790214123695620865513992469148710987667 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5479399473547213650679001711688779909751205673917159 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P004_replay :
    compactExp2620 momentScalarGrow2622K03P004Input 20 = momentScalarGrow2622K03P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P004] using h

theorem momentScalarGrow2622K03P004_radius_le :
    (momentScalarGrow2622K03P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P004Expected]

end ConnesWeilRH.Dev
