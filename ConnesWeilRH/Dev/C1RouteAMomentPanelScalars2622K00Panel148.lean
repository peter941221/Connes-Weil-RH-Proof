import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P148 : ℚ := ((-5310566383167203229259349008960119887684075709402627723 : ℚ) / 120167404936916833377678598854994132906772628557004800)

def momentPanelGrowth2622K00P148 : ℚ := ((27729021968103677660664745304187846655654059102949937677 : ℚ) / 32348938897782530088987221805296088575254302640884940800)

theorem momentPanelPhase_owner2622K00P148 :
    (momentPanelPhase2622K00P148 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (117 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P148 :
    (momentPanelGrowth2622K00P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P148Input : RatPair2542 := (momentPanelPhase2622K00P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P148Expected : RatState2542 :=
  ((((137022766917323544330005880820888791590829492886362507349589520391749857018791 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((173706731331363648043198013119 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P148_replay :
    compactExp2620 momentScalarAmp2622K00P148Input 20 = momentScalarAmp2622K00P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K00P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P148_replay] at h
  simpa only [momentPanelPhase_owner2622K00P148] using h

theorem momentScalarAmp2622K00P148_radius_le :
    (momentScalarAmp2622K00P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [momentScalarAmp2622K00P148Expected]

def momentScalarGrow2622K00P148Input : RatPair2542 := (momentPanelGrowth2622K00P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P148Expected : RatState2542 :=
  ((((1258372716047067406772604741091849273208063028287565161729431794896670569490363212446842368859689 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6380702499163232760784694195967295540530288240017 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P148_replay :
    compactExp2620 momentScalarGrow2622K00P148Input 20 = momentScalarGrow2622K00P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P148] using h

theorem momentScalarGrow2622K00P148_radius_le :
    (momentScalarGrow2622K00P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P148Expected]

end ConnesWeilRH.Dev
