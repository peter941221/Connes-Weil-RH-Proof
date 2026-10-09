import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P136 : ℚ := ((-5319557136696409732407895088918297534959925644580304147 : ℚ) / 143186055724878554339386634970275590466353566108876800)

def momentPanelGrowth2622K00P136 : ℚ := ((22583585106201376890824306399054785038153959922897941917 : ℚ) / 46204522482793488842152480401258720207724914123001036800)

theorem momentPanelPhase_owner2622K00P136 :
    (momentPanelPhase2622K00P136 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (93 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P136 :
    (momentPanelGrowth2622K00P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P136Input : RatPair2542 := (momentPanelPhase2622K00P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P136Expected : RatState2542 :=
  ((((156663077820907501527622891146464286200636713682851601944435526585767374475950993 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((198601083422502807474586292877591 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P136_replay :
    compactExp2620 momentScalarAmp2622K00P136Input 20 = momentScalarAmp2622K00P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K00P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P136_replay] at h
  simpa only [momentPanelPhase_owner2622K00P136] using h

theorem momentScalarAmp2622K00P136_radius_le :
    (momentScalarAmp2622K00P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P136Expected]

def momentScalarGrow2622K00P136Input : RatPair2542 := (momentPanelGrowth2622K00P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P136Expected : RatState2542 :=
  ((((3482335517679248403050978837981989888900807276492088096227970023342248814419570356293294529467309 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4414382651498730795028260587247708024248597054799 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P136_replay :
    compactExp2620 momentScalarGrow2622K00P136Input 20 = momentScalarGrow2622K00P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P136] using h

theorem momentScalarGrow2622K00P136_radius_le :
    (momentScalarGrow2622K00P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P136Expected]

end ConnesWeilRH.Dev
