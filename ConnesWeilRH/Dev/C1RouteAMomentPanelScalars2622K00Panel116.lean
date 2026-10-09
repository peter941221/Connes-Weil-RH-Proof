import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P116 : ℚ := ((-1790578973065933064290860127548004566342443592135697689 : ℚ) / 56619486868722510865534627722449251858358111672729600)

def momentPanelGrowth2622K00P116 : ℚ := ((41742627087181109843402083266209052098960976514860364711 : ℚ) / 196278393363203905704237254502825733911341759793096294400)

theorem momentPanelPhase_owner2622K00P116 :
    (momentPanelPhase2622K00P116 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (53 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P116 :
    (momentPanelGrowth2622K00P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P116Input : RatPair2542 := (momentPanelPhase2622K00P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P116Expected : RatState2542 :=
  ((((39366786221133433886394671484286057668344352803716554822850272177915300015752801691 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((49904835279008419877432216624213111 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P116_replay :
    compactExp2620 momentScalarAmp2622K00P116Input 20 = momentScalarAmp2622K00P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K00P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P116_replay] at h
  simpa only [momentPanelPhase_owner2622K00P116] using h

theorem momentScalarAmp2622K00P116_radius_le :
    (momentScalarAmp2622K00P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P116Expected]

def momentScalarGrow2622K00P116Input : RatPair2542 := (momentPanelGrowth2622K00P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P116Expected : RatState2542 :=
  ((((330270859611541174282088658124963975400180405543049926101004028950452070308824052426731930436041 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((837335937021767634579716668033124845508069100871 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P116_replay :
    compactExp2620 momentScalarGrow2622K00P116Input 20 = momentScalarGrow2622K00P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P116] using h

theorem momentScalarGrow2622K00P116_radius_le :
    (momentScalarGrow2622K00P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P116Expected]

end ConnesWeilRH.Dev
