import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P166 : ℚ := ((-5340396565776973545007404455050528352104619842509094767 : ℚ) / 75774292702990657237241672061237036184723677564108800)

def momentPanelGrowth2622P166 : ℚ := ((35472574382893709049581191917542783844265055168165579437 : ℚ) / 12615378415131346161671518272752656173104987462487244800)

theorem momentPanelPhase_owner2622P166 :
    (momentPanelPhase2622P166 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (153 / 200) 0 := by
  norm_num [momentPanelPhase2622P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P166 :
    (momentPanelGrowth2622P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P166Input : RatPair2542 := (momentPanelPhase2622P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P166Expected : RatState2542 :=
  ((((526659440721625791856497030640718873023563631448597448611497365235 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417852306894290995902507 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P166_replay :
    compactExp2620 momentScalarAmp2622P166Input 20 = momentScalarAmp2622P166Expected := by
  decide +kernel

theorem momentScalarAmp2622P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P166]
  have h := compactExp_real_error2620 momentPanelPhase2622P166 20 hsmall
  change |Real.exp (momentPanelPhase2622P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P166_replay] at h
  simpa only [momentPanelPhase_owner2622P166] using h

theorem momentScalarAmp2622P166_radius_le :
    (momentScalarAmp2622P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P166Expected]

def momentScalarGrow2622P166Input : RatPair2542 := (momentPanelGrowth2622P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P166Expected : RatState2542 :=
  ((((17772164862711135254569258571173356587423903949966365464944338344534628072488763142435597576400161 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((45057670084744533216827764019722611627372421015089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P166_replay :
    compactExp2620 momentScalarGrow2622P166Input 20 = momentScalarGrow2622P166Expected := by
  decide +kernel

theorem momentScalarGrow2622P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P166_replay] at h
  simpa only [momentPanelGrowth_owner2622P166] using h

theorem momentScalarGrow2622P166_radius_le :
    (momentScalarGrow2622P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622P166Expected]

end ConnesWeilRH.Dev
