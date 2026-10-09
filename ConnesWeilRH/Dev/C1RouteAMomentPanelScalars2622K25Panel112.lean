import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P112 : ℚ := ((-19256386951187688924400015123350400401 : ℚ) / 616179603758937747479517494069166080)

def momentPanelGrowth2622K25P112 : ℚ := ((5134583646497219298081583799754303735443 : ℚ) / 30322148609073797606874517212378012057600)

theorem momentPanelPhase_owner2622K25P112 :
    (momentPanelPhase2622K25P112 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P112 :
    (momentPanelGrowth2622K25P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P112Input : RatPair2542 := (momentPanelPhase2622K25P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P112Expected : RatState2542 :=
  ((((57193975979939167320515866085103188266967890655354062547216606939345310286525879167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((36252069414619323592411765998570045 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K25P112_replay :
    compactExp2620 momentScalarAmp2622K25P112Input 20 = momentScalarAmp2622K25P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K25P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P112_replay] at h
  simpa only [momentPanelPhase_owner2622K25P112] using h

theorem momentScalarAmp2622K25P112_radius_le :
    (momentScalarAmp2622K25P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P112Expected]

def momentScalarGrow2622K25P112Input : RatPair2542 := (momentPanelGrowth2622K25P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P112Expected : RatState2542 :=
  ((((2530111260626328888340574270985429532037848955587162839962430790212608891102852036188042805664311 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3207296540231149552877195700272634444070363501545 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K25P112_replay :
    compactExp2620 momentScalarGrow2622K25P112Input 20 = momentScalarGrow2622K25P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P112] using h

theorem momentScalarGrow2622K25P112_radius_le :
    (momentScalarGrow2622K25P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P112Expected]

end ConnesWeilRH.Dev
