import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P088 : ℚ := ((-219257687142598223976341758516769775729557387891412525 : ℚ) / 7305863997312517325235445018144609279882549790769152)

def momentPanelGrowth2622K03P088 : ℚ := ((2846493705366488756714005773032289597661267585404475 : ℚ) / 190147483054856792814269374666625420292381633058701312)

theorem momentPanelPhase_owner2622K03P088 :
    (momentPanelPhase2622K03P088 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P088 :
    (momentPanelGrowth2622K03P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P088Input : RatPair2542 := (momentPanelPhase2622K03P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P088Expected : RatState2542 :=
  ((((98826527631887138685544383917683624929362910404965101202751108307592440493566844871 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((62640546339466757100622787899560941 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P088_replay :
    compactExp2620 momentScalarAmp2622K03P088Input 20 = momentScalarAmp2622K03P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K03P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P088_replay] at h
  simpa only [momentPanelPhase_owner2622K03P088] using h

theorem momentScalarAmp2622K03P088_radius_le :
    (momentScalarAmp2622K03P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P088Expected]

def momentScalarGrow2622K03P088Input : RatPair2542 := (momentPanelGrowth2622K03P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P088Expected : RatState2542 :=
  ((((1084101568988854281819389106604985957286415693476195277160950082525231891126338778675349072833543 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2748523970035052240594153957839216333928369122755 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P088_replay :
    compactExp2620 momentScalarGrow2622K03P088Input 20 = momentScalarGrow2622K03P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P088] using h

theorem momentScalarGrow2622K03P088_radius_le :
    (momentScalarGrow2622K03P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P088Expected]

end ConnesWeilRH.Dev
