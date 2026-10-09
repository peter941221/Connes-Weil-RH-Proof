import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P103 : ℚ := ((-5422054179796791833502739779625702426136949417090858693 : ℚ) / 179358221248818401564927834580003595202837896547532800)

def momentPanelGrowth2622K00P103 : ℚ := ((510255166567470410630103332860178790128435043914293957 : ℚ) / 4572826248751720584229028368616995483627119174274252800)

theorem momentPanelPhase_owner2622K00P103 :
    (momentPanelPhase2622K00P103 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P103 :
    (momentPanelGrowth2622K00P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P103Input : RatPair2542 := (momentPanelPhase2622K00P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P103Expected : RatState2542 :=
  ((((158760654963378826876790478651971012264564963263628085866032105052278858199126718763 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((201258841741541019564057726208251337 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P103_replay :
    compactExp2620 momentScalarAmp2622K00P103Input 20 = momentScalarAmp2622K00P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K00P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P103_replay] at h
  simpa only [momentPanelPhase_owner2622K00P103] using h

theorem momentScalarAmp2622K00P103_radius_le :
    (momentScalarAmp2622K00P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P103Expected]

def momentScalarGrow2622K00P103Input : RatPair2542 := (momentPanelGrowth2622K00P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P103Expected : RatState2542 :=
  ((((149258486289237549170368464688835618578250900149260540428197067768968795577070979019490149102917 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3027321433586953862751681843120734618067330451597 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P103_replay :
    compactExp2620 momentScalarGrow2622K00P103Input 20 = momentScalarGrow2622K00P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P103] using h

theorem momentScalarGrow2622K00P103_radius_le :
    (momentScalarGrow2622K00P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P103Expected]

end ConnesWeilRH.Dev
