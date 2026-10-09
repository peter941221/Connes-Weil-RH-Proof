import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P125 : ℚ := ((-72851357092551666405005974741480577943903779300826725 : ℚ) / 2128859822477126463228442419455355753506322740412416)

def momentPanelGrowth2622K03P125 : ℚ := ((7604649137023445708299784609079504693184241154825 : ℚ) / 26398373324289433960054057290937862042535281557504)

theorem momentPanelPhase_owner2622K03P125 :
    (momentPanelPhase2622K03P125 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (71 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P125 :
    (momentPanelGrowth2622K03P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P125Input : RatPair2542 := (momentPanelPhase2622K03P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P125Expected : RatState2542 :=
  ((((2935482843659268404578006902405131537605383832672032283490800411048283859789911573 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3721288035366974336152829895697007 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P125_replay :
    compactExp2620 momentScalarAmp2622K03P125Input 20 = momentScalarAmp2622K03P125Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622K03P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P125]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P125 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P125_replay] at h
  simpa only [momentPanelPhase_owner2622K03P125] using h

theorem momentScalarAmp2622K03P125_radius_le :
    (momentScalarAmp2622K03P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P125Expected]

def momentScalarGrow2622K03P125Input : RatPair2542 := (momentPanelGrowth2622K03P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P125Expected : RatState2542 :=
  ((((2849095265945865770635288000440846051270125504218364115946067821630552643140431717330431018252019 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3611656331762306412323548618284182733025558951597 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P125_replay :
    compactExp2620 momentScalarGrow2622K03P125Input 20 = momentScalarGrow2622K03P125Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P125_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P125] using h

theorem momentScalarGrow2622K03P125_radius_le :
    (momentScalarGrow2622K03P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P125Expected]

end ConnesWeilRH.Dev
