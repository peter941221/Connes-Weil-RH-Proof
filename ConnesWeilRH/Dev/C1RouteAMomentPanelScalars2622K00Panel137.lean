import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P137 : ℚ := ((-14181510726749503606859630798824949855818072656452063 : ℚ) / 377250110136039315761326147444890554448687587655680)

def momentPanelGrowth2622K00P137 : ℚ := ((269686068042961448986639840064026281871977988966527031 : ℚ) / 528335125491429734466441760284487430797837826680422400)

theorem momentPanelPhase_owner2622K00P137 :
    (momentPanelPhase2622K00P137 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P137, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P137 :
    (momentPanelGrowth2622K00P137 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P137, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P137Input : RatPair2542 := (momentPanelPhase2622K00P137 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P137Expected : RatState2542 :=
  ((((100852638713696759258216642397612518602356915118977432625605727974902616167498159 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((127850493818563424056707088075257 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P137_replay :
    compactExp2620 momentScalarAmp2622K00P137Input 20 = momentScalarAmp2622K00P137Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P137_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 40) 0) -
      (momentScalarAmp2622K00P137Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P137]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P137 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P137 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P137Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P137_replay] at h
  simpa only [momentPanelPhase_owner2622K00P137] using h

theorem momentScalarAmp2622K00P137_radius_le :
    (momentScalarAmp2622K00P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P137Expected]

def momentScalarGrow2622K00P137Input : RatPair2542 := (momentPanelGrowth2622K00P137 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P137Expected : RatState2542 :=
  ((((3558623941164142895704358273948109896370443417321394944402796831368582038526684828198043635790863 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2255544789505847949724102773860144134641780877049 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P137_replay :
    compactExp2620 momentScalarGrow2622K00P137Input 20 = momentScalarGrow2622K00P137Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P137_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P137Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P137]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P137 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P137 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P137Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P137_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P137] using h

theorem momentScalarGrow2622K00P137_radius_le :
    (momentScalarGrow2622K00P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P137Expected]

end ConnesWeilRH.Dev
