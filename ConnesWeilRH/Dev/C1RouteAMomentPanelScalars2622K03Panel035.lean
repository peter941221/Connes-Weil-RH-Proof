import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P035 : ℚ := ((-73351345104596468353684751835646818421630790936420225 : ℚ) / 1712331855837819131540392242131215092904381965664256)

def momentPanelGrowth2622K03P035 : ℚ := ((1614668052347660491158042255676141541779005311237075 : ℚ) / 2370098936489058626164438147155587219438280105787392)

theorem momentPanelPhase_owner2622K03P035 :
    (momentPanelPhase2622K03P035 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P035 :
    (momentPanelGrowth2622K03P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P035Input : RatPair2542 := (momentPanelPhase2622K03P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P035Expected : RatState2542 :=
  ((((33232184243533994663548484676579226385330527499887711619186669025737816758797 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((84257340890874133980043861743 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P035_replay :
    compactExp2620 momentScalarAmp2622K03P035Input 20 = momentScalarAmp2622K03P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K03P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P035_replay] at h
  simpa only [momentPanelPhase_owner2622K03P035] using h

theorem momentScalarAmp2622K03P035_radius_le :
    (momentScalarAmp2622K03P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P035Expected]

def momentScalarGrow2622K03P035Input : RatPair2542 := (momentPanelGrowth2622K03P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P035Expected : RatState2542 :=
  ((((4221518717276826731759786034240067417017432157701473370454823638388871548944012771854298123425741 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5351407258988250191352852931747117926130875619215 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P035_replay :
    compactExp2620 momentScalarGrow2622K03P035Input 20 = momentScalarGrow2622K03P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P035] using h

theorem momentScalarGrow2622K03P035_radius_le :
    (momentScalarGrow2622K03P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P035Expected]

end ConnesWeilRH.Dev
