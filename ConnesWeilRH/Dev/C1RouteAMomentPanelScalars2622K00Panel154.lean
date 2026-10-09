import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P154 : ℚ := ((-5314161491292028982582941797015952167670577272480974519 : ℚ) / 106685052332539253957249606273186422050446650848051200)

def momentPanelGrowth2622K00P154 : ℚ := ((48481441793011485329153485644462564727420415404949677 : ℚ) / 40618327536257453447013972061757071985343862721740800)

theorem momentPanelPhase_owner2622K00P154 :
    (momentPanelPhase2622K00P154 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (129 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P154 :
    (momentPanelGrowth2622K00P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P154Input : RatPair2542 := (momentPanelPhase2622K00P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P154Expected : RatState2542 :=
  ((((124337365692890052677037359497580788932389729494829946389601726797375935405 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((632913147056455854056738511 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P154_replay :
    compactExp2620 momentScalarAmp2622K00P154Input 20 = momentScalarAmp2622K00P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K00P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P154_replay] at h
  simpa only [momentPanelPhase_owner2622K00P154] using h

theorem momentScalarAmp2622K00P154_radius_le :
    (momentScalarAmp2622K00P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [momentScalarAmp2622K00P154Expected]

def momentScalarGrow2622K00P154Input : RatPair2542 := (momentPanelGrowth2622K00P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P154Expected : RatState2542 :=
  ((((7046381544329549729081964039309413031473300649230466741352913423975997766169740936733879318189623 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4466169813246229986390206400432581630273995444053 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P154_replay :
    compactExp2620 momentScalarGrow2622K00P154Input 20 = momentScalarGrow2622K00P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P154] using h

theorem momentScalarGrow2622K00P154_radius_le :
    (momentScalarGrow2622K00P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P154Expected]

end ConnesWeilRH.Dev
