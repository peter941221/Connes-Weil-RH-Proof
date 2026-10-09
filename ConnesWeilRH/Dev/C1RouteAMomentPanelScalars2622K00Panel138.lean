import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P138 : ℚ := ((-1772233955474276566432067178624836062584412965663565661 : ℚ) / 46571663112072553302884294497524806098223575439769600)

def momentPanelGrowth2622K00P138 : ℚ := ((23442609748860925341052246328294142998407376494053865757 : ℚ) / 43955271462941229251037009443708360640474433939360972800)

theorem momentPanelPhase_owner2622K00P138 :
    (momentPanelPhase2622K00P138 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (97 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P138 :
    (momentPanelGrowth2622K00P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P138Input : RatPair2542 := (momentPanelPhase2622K00P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P138Expected : RatState2542 :=
  ((((63532325057920557700688247999083977583056616978698456452658280619806673142538207 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((80539715228179171962175492989873 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P138_replay :
    compactExp2620 momentScalarAmp2622K00P138Input 20 = momentScalarAmp2622K00P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K00P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P138_replay] at h
  simpa only [momentPanelPhase_owner2622K00P138] using h

theorem momentScalarAmp2622K00P138_radius_le :
    (momentScalarAmp2622K00P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P138Expected]

def momentScalarGrow2622K00P138Input : RatPair2542 := (momentPanelGrowth2622K00P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P138Expected : RatState2542 :=
  ((((227562324135916023688696430373851944920107904721610321913524018328447011184426947495417723141033 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((4615509920933455336394872048522411269579541873323 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P138_replay :
    compactExp2620 momentScalarGrow2622K00P138Input 20 = momentScalarGrow2622K00P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P138] using h

theorem momentScalarGrow2622K00P138_radius_le :
    (momentScalarGrow2622K00P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P138Expected]

end ConnesWeilRH.Dev
