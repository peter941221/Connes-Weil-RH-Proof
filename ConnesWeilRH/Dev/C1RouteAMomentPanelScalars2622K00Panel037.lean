import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P037 : ℚ := ((-45189651379594768567422931552434797409265251840387669 : ℚ) / 1058675248541572801373794200698857512363266135818240)

def momentPanelGrowth2622K00P037 : ℚ := ((25158365271666303431532166192918317209758152950352237517 : ℚ) / 39361954504514867741987603475085172645073294948355276800)

theorem momentPanelPhase_owner2622K00P037 :
    (momentPanelPhase2622K00P037 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P037 :
    (momentPanelGrowth2622K00P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P037Input : RatPair2542 := (momentPanelPhase2622K00P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P037Expected : RatState2542 :=
  ((((77376361019103069458669024727074346346381078662060540319407497818350478509313 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((392361942652050871102125829323 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P037_replay :
    compactExp2620 momentScalarAmp2622K00P037Input 20 = momentScalarAmp2622K00P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K00P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P037_replay] at h
  simpa only [momentPanelPhase_owner2622K00P037] using h

theorem momentScalarAmp2622K00P037_radius_le :
    (momentScalarAmp2622K00P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarAmp2622K00P037Expected]

def momentScalarGrow2622K00P037Input : RatPair2542 := (momentPanelGrowth2622K00P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P037Expected : RatState2542 :=
  ((((1011858624108520427783768880514100505333052951000472899488074726293328153792837243699873178679961 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1282682410344249901602566169250747320983806756927 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P037_replay :
    compactExp2620 momentScalarGrow2622K00P037Input 20 = momentScalarGrow2622K00P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P037] using h

theorem momentScalarGrow2622K00P037_radius_le :
    (momentScalarGrow2622K00P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P037Expected]

end ConnesWeilRH.Dev
