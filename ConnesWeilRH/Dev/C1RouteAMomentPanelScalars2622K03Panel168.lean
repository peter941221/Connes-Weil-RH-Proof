import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P168 : ℚ := ((-72857845238900003890785792470654640298027900141696175 : ℚ) / 934812984777778779056031911126152526447425852801024)

def momentPanelGrowth2622K03P168 : ℚ := ((1444506491290399038291740904485729139641673350836537475 : ℚ) / 430232010773297542444884191349011022638810811724726272)

theorem momentPanelPhase_owner2622K03P168 :
    (momentPanelPhase2622K03P168 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P168 :
    (momentPanelGrowth2622K03P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P168Input : RatPair2542 := (momentPanelPhase2622K03P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P168Expected : RatState2542 :=
  ((((151475960225157829070704267577055727084588010445149778660352549 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639613324136527311 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P168_replay :
    compactExp2620 momentScalarAmp2622K03P168Input 20 = momentScalarAmp2622K03P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K03P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P168_replay] at h
  simpa only [momentPanelPhase_owner2622K03P168] using h

theorem momentScalarAmp2622K03P168_radius_le :
    (momentScalarAmp2622K03P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P168Expected]

def momentScalarGrow2622K03P168Input : RatPair2542 := (momentPanelGrowth2622K03P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P168Expected : RatState2542 :=
  ((((61340155744165291351162497011098577337263295981597542548627463027938406114189035145799863237091249 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((77757636269393074141738782463237530222503017144907 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P168_replay :
    compactExp2620 momentScalarGrow2622K03P168Input 20 = momentScalarGrow2622K03P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P168] using h

theorem momentScalarGrow2622K03P168_radius_le :
    (momentScalarGrow2622K03P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P168Expected]

end ConnesWeilRH.Dev
