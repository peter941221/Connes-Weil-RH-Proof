import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P067 : ℚ := ((-19685839487823518289578707345800319599 : ℚ) / 616179603758937747479517494069166080)

def momentPanelGrowth2622K28P067 : ℚ := ((5134583646497219298081583799754303735443 : ℚ) / 30322148609073797606874517212378012057600)

theorem momentPanelPhase_owner2622K28P067 :
    (momentPanelPhase2622K28P067 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P067 :
    (momentPanelGrowth2622K28P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P067Input : RatPair2542 := (momentPanelPhase2622K28P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P067Expected : RatState2542 :=
  ((((14244080219987187507149544265794807735751396454222436506436687273014070721957504315 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((36114133999216704610585454117930837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K28P067_replay :
    compactExp2620 momentScalarAmp2622K28P067Input 20 = momentScalarAmp2622K28P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K28P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P067_replay] at h
  simpa only [momentPanelPhase_owner2622K28P067] using h

theorem momentScalarAmp2622K28P067_radius_le :
    (momentScalarAmp2622K28P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P067Expected]

def momentScalarGrow2622K28P067Input : RatPair2542 := (momentPanelGrowth2622K28P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P067Expected : RatState2542 :=
  ((((2530111260626328888340574270985429532037848955587162839962430790212608891102852036188042805664311 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3207296540231149552877195700272634444070363501545 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K28P067_replay :
    compactExp2620 momentScalarGrow2622K28P067Input 20 = momentScalarGrow2622K28P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P067] using h

theorem momentScalarGrow2622K28P067_radius_le :
    (momentScalarGrow2622K28P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P067Expected]

end ConnesWeilRH.Dev
