import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P109 : ℚ := ((-5397726375471375888506264665614107888304633750432903249 : ℚ) / 175741004696424416842373714619030794729189463503667200)

def momentPanelGrowth2622K00P109 : ℚ := ((1057764093614549345889751986291896104462965629413 : ℚ) / 6850788924988607429079772653357576654637183795200)

theorem momentPanelPhase_owner2622K00P109 :
    (momentPanelPhase2622K00P109 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (39 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P109, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P109 :
    (momentPanelGrowth2622K00P109 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P109, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P109Input : RatPair2542 := (momentPanelPhase2622K00P109 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P109Expected : RatState2542 :=
  ((((97866824299812993117621952756618823894504309993010628689126794297804641295838159073 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((124064572521205593753135043198879815 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P109_replay :
    compactExp2620 momentScalarAmp2622K00P109Input 20 = momentScalarAmp2622K00P109Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P109_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (39 / 200) 0) -
      (momentScalarAmp2622K00P109Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P109]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P109 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P109 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P109Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P109_replay] at h
  simpa only [momentPanelPhase_owner2622K00P109] using h

theorem momentScalarAmp2622K00P109_radius_le :
    (momentScalarAmp2622K00P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P109Expected]

def momentScalarGrow2622K00P109Input : RatPair2542 := (momentPanelGrowth2622K00P109 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P109Expected : RatState2542 :=
  ((((2492607085667527187598616508261817394991630468223884496647228469326181446918446043375305346345507 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3159754403013189633686739702875121929992104918187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P109_replay :
    compactExp2620 momentScalarGrow2622K00P109Input 20 = momentScalarGrow2622K00P109Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P109_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P109Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P109]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P109 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P109 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P109Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P109_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P109] using h

theorem momentScalarGrow2622K00P109_radius_le :
    (momentScalarGrow2622K00P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P109Expected]

end ConnesWeilRH.Dev
