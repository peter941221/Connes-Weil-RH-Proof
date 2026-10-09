import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P004 : ℚ := ((-5582269845225765897186300327253822319531336012654384619 : ℚ) / 49138425362634951552979515984982778151494306968371200)

def momentPanelGrowth2622K00P004 : ℚ := ((2462670293232322169044383381226001182443176309442468757 : ℚ) / 322596799688788535227937414473954927090210347732172800)

theorem momentPanelPhase_owner2622K00P004 :
    (momentPanelPhase2622K00P004 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-171 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P004 :
    (momentPanelGrowth2622K00P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P004Input : RatPair2542 := (momentPanelPhase2622K00P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P004Expected : RatState2542 :=
  ((((49140138351715465715316923774069899032542198343 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614629174706177 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P004_replay :
    compactExp2620 momentScalarAmp2622K00P004Input 20 = momentScalarAmp2622K00P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K00P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P004_replay] at h
  simpa only [momentPanelPhase_owner2622K00P004] using h

theorem momentScalarAmp2622K00P004_radius_le :
    (momentScalarAmp2622K00P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P004Expected]

def momentScalarGrow2622K00P004Input : RatPair2542 := (momentPanelGrowth2622K00P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P004Expected : RatState2542 :=
  ((((1103817716708000300600740725562692260934154427765469810041917191482476979631258226702573251972235341 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2798490008473354577680694917148053829837059422145523 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P004_replay :
    compactExp2620 momentScalarGrow2622K00P004Input 20 = momentScalarGrow2622K00P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P004] using h

theorem momentScalarGrow2622K00P004_radius_le :
    (momentScalarGrow2622K00P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [momentScalarGrow2622K00P004Expected]

end ConnesWeilRH.Dev
