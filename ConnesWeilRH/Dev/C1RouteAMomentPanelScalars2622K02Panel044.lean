import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P044 : ℚ := ((-119794139165785041249747947480524047930188065064206097 : ℚ) / 3018057970996022764485851510997902415394956011110400)

def momentPanelGrowth2622K02P044 : ℚ := ((89623053290809076176156461357706251532204145881288013 : ℚ) / 184821011792650463009678424128071537837342859250892800)

theorem momentPanelPhase_owner2622K02P044 :
    (momentPanelPhase2622K02P044 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P044 :
    (momentPanelGrowth2622K02P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P044Input : RatPair2542 := (momentPanelPhase2622K02P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P044Expected : RatState2542 :=
  ((((6170965907886818270908797997149063317854086227734816593050535555964056276402603 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15645851933828902453183089651091 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P044_replay :
    compactExp2620 momentScalarAmp2622K02P044Input 20 = momentScalarAmp2622K02P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K02P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P044_replay] at h
  simpa only [momentPanelPhase_owner2622K02P044] using h

theorem momentScalarAmp2622K02P044_radius_le :
    (momentScalarAmp2622K02P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P044Expected]

def momentScalarGrow2622K02P044Input : RatPair2542 := (momentPanelGrowth2622K02P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P044Expected : RatState2542 :=
  ((((1734466317354055806300973854576626468288728508216119241169444793828796024170356467147597484221257 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4397392502947096272238722592589115461930562221553 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P044_replay :
    compactExp2620 momentScalarGrow2622K02P044Input 20 = momentScalarGrow2622K02P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P044] using h

theorem momentScalarGrow2622K02P044_radius_le :
    (momentScalarGrow2622K02P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P044Expected]

end ConnesWeilRH.Dev
