import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P046 : ℚ := ((-2478205553716833420165001606650417537393 : ℚ) / 65777882585602732351903330645678489600)

def momentPanelGrowth2622K10P046 : ℚ := ((565473578735688096690067508033383187 : ℚ) / 1341681395281557998544110672569958400)

theorem momentPanelPhase_owner2622K10P046 :
    (momentPanelPhase2622K10P046 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P046 :
    (momentPanelGrowth2622K10P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P046Input : RatPair2542 := (momentPanelPhase2622K10P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P046Expected : RatState2542 :=
  ((((92767678472433938591448540097413358039269341006710424523276639586301990747396201 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((117601231054426797242433427726705 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K10P046_replay :
    compactExp2620 momentScalarAmp2622K10P046Input 20 = momentScalarAmp2622K10P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K10P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P046_replay] at h
  simpa only [momentPanelPhase_owner2622K10P046] using h

theorem momentScalarAmp2622K10P046_radius_le :
    (momentScalarAmp2622K10P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P046Expected]

def momentScalarGrow2622K10P046Input : RatPair2542 := (momentPanelGrowth2622K10P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P046Expected : RatState2542 :=
  ((((3255660635629621980633427084897664175376963068379318378227385144774808111873883120430164831291269 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4127038500066327363712766932907920429670747605321 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K10P046_replay :
    compactExp2620 momentScalarGrow2622K10P046Input 20 = momentScalarGrow2622K10P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P046] using h

theorem momentScalarGrow2622K10P046_radius_le :
    (momentScalarGrow2622K10P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P046Expected]

end ConnesWeilRH.Dev
