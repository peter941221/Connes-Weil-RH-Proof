import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P114 : ℚ := ((-72909020310697768576073867192737229638808850269904275 : ℚ) / 2289625002583525784230847751054146885668475320139776)

def momentPanelGrowth2622K03P114 : ℚ := ((5947409186675722915935171457241450441403813331279 : ℚ) / 34253944624943037145398863266787883273185918976000)

theorem momentPanelPhase_owner2622K03P114 :
    (momentPanelPhase2622K03P114 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (49 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P114, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P114 :
    (momentPanelGrowth2622K03P114 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P114, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P114Input : RatPair2542 := (momentPanelPhase2622K03P114 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P114Expected : RatState2542 :=
  ((((31642167534689627706628144803305657096080609270650866912636077131579880587596414385 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1253513462135448322974658757851725 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K03P114_replay :
    compactExp2620 momentScalarAmp2622K03P114Input 20 = momentScalarAmp2622K03P114Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P114_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (49 / 200) 0) -
      (momentScalarAmp2622K03P114Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P114]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P114 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P114 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P114Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P114_replay] at h
  simpa only [momentPanelPhase_owner2622K03P114] using h

theorem momentScalarAmp2622K03P114_radius_le :
    (momentScalarAmp2622K03P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P114Expected]

def momentScalarGrow2622K03P114Input : RatPair2542 := (momentPanelGrowth2622K03P114 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P114Expected : RatState2542 :=
  ((((2540995258708698747407214255186769856468785638944829001896330078338189081327850638007466312101257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3221093631518850503139596660925679288128343592957 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P114_replay :
    compactExp2620 momentScalarGrow2622K03P114Input 20 = momentScalarGrow2622K03P114Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P114_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P114Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P114]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P114 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P114 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P114Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P114_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P114] using h

theorem momentScalarGrow2622K03P114_radius_le :
    (momentScalarGrow2622K03P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P114Expected]

end ConnesWeilRH.Dev
