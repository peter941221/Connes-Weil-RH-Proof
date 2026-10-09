import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P033 : ℚ := ((-1883541654180100158138809838019565856050563532783301171 : ℚ) / 41456407381414393089171397583017815529427811539353600)

def momentPanelGrowth2622K00P033 : ℚ := ((80616829068064031174726235220207654957231637987025292471 : ℚ) / 104077187632023232392115715843065855656440314429072998400)

theorem momentPanelPhase_owner2622K00P033 :
    (momentPanelPhase2622K00P033 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-113 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P033, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P033 :
    (momentPanelGrowth2622K00P033 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P033, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P033Input : RatPair2542 := (momentPanelPhase2622K00P033 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P033Expected : RatState2542 :=
  ((((39604575210215127161718631233741231235732189943101547121085413316168703662417 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((50209356782957716427977235571 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P033_replay :
    compactExp2620 momentScalarAmp2622K00P033Input 20 = momentScalarAmp2622K00P033Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P033_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-113 / 200) 0) -
      (momentScalarAmp2622K00P033Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P033]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P033 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P033 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P033Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P033_replay] at h
  simpa only [momentPanelPhase_owner2622K00P033] using h

theorem momentScalarAmp2622K00P033_radius_le :
    (momentScalarAmp2622K00P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [momentScalarAmp2622K00P033Expected]

def momentScalarGrow2622K00P033Input : RatPair2542 := (momentPanelGrowth2622K00P033 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P033Expected : RatState2542 :=
  ((((2317220945721681509957869839464086977433315837254437645371182631143974144062027983188352673759615 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5874848705637190478363733467432056293923710697345 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P033_replay :
    compactExp2620 momentScalarGrow2622K00P033Input 20 = momentScalarGrow2622K00P033Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P033_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P033Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P033]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P033 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P033 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P033Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P033_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P033] using h

theorem momentScalarGrow2622K00P033_radius_le :
    (momentScalarGrow2622K00P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P033Expected]

end ConnesWeilRH.Dev
