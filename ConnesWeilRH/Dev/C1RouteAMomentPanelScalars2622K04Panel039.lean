import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P039 : ℚ := ((-127739479680283189527492269761599856058000223624177791 : ℚ) / 2835370266329659899710390906908367037937964443238400)

def momentPanelGrowth2622K04P039 : ℚ := ((5107312277580404336488502425110725163554384879136498927 : ℚ) / 7813496181397400758647195811299247058979587686295142400)

theorem momentPanelPhase_owner2622K04P039 :
    (momentPanelPhase2622K04P039 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P039 :
    (momentPanelGrowth2622K04P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P039Input : RatPair2542 := (momentPanelPhase2622K04P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P039Expected : RatState2542 :=
  ((((58037092555827284744570817400755089350368515111782920249291059538503420735621 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18394083526386273466937158975 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P039_replay :
    compactExp2620 momentScalarAmp2622K04P039Input 20 = momentScalarAmp2622K04P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K04P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P039_replay] at h
  simpa only [momentPanelPhase_owner2622K04P039] using h

theorem momentScalarAmp2622K04P039_radius_le :
    (momentScalarAmp2622K04P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P039Expected]

def momentScalarGrow2622K04P039Input : RatPair2542 := (momentPanelGrowth2622K04P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P039Expected : RatState2542 :=
  ((((4106542671042070774527691736862560137004268658228609162494845320847439242633055420112425097226325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5205658036748307850774610694988542500090652663111 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P039_replay :
    compactExp2620 momentScalarGrow2622K04P039Input 20 = momentScalarGrow2622K04P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P039] using h

theorem momentScalarGrow2622K04P039_radius_le :
    (momentScalarGrow2622K04P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P039Expected]

end ConnesWeilRH.Dev
