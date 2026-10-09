import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P142 : ℚ := ((-42500446860259406524798158410542183770090700738172331 : ℚ) / 1058675248541572801373794200698857512363266135818240)

def momentPanelGrowth2622K00P142 : ℚ := ((25158365271666303431532166192918317209758152950352237517 : ℚ) / 39361954504514867741987603475085172645073294948355276800)

theorem momentPanelPhase_owner2622K00P142 :
    (momentPanelPhase2622K00P142 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P142 :
    (momentPanelGrowth2622K00P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P142Input : RatPair2542 := (momentPanelPhase2622K00P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P142Expected : RatState2542 :=
  ((((7850110306314425586119839653110524092427525800979072622726079870102515357423181 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4975790225143124576247126131843 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P142_replay :
    compactExp2620 momentScalarAmp2622K00P142Input 20 = momentScalarAmp2622K00P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K00P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P142_replay] at h
  simpa only [momentPanelPhase_owner2622K00P142] using h

theorem momentScalarAmp2622K00P142_radius_le :
    (momentScalarAmp2622K00P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622K00P142Expected]

def momentScalarGrow2622K00P142Input : RatPair2542 := (momentPanelGrowth2622K00P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P142Expected : RatState2542 :=
  ((((1011858624108520427783768880514100505333052951000472899488074726293328153792837243699873178679961 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1282682410344249901602566169250747320983806756927 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P142_replay :
    compactExp2620 momentScalarGrow2622K00P142Input 20 = momentScalarGrow2622K00P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P142] using h

theorem momentScalarGrow2622K00P142_radius_le :
    (momentScalarGrow2622K00P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P142Expected]

end ConnesWeilRH.Dev
