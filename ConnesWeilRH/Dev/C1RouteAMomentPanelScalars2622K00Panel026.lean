import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P026 : ℚ := ((-1882704033100307176518975892286845205900656705390807869 : ℚ) / 36341151650756232875458500668510824960632047638937600)

def momentPanelGrowth2622K00P026 : ℚ := ((116687209424428515638297180086693824626080828380829277 : ℚ) / 103645585646152641794547880472646777208005953637580800)

theorem momentPanelPhase_owner2622K00P026 :
    (momentPanelPhase2622K00P026 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-127 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P026 :
    (momentPanelGrowth2622K00P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P026Input : RatPair2542 := (momentPanelPhase2622K00P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P026Expected : RatState2542 :=
  ((((67665520110261840837776297907218482724147302713561350591406310311098715851 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((44099163411968917043433533 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P026_replay :
    compactExp2620 momentScalarAmp2622K00P026Input 20 = momentScalarAmp2622K00P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K00P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P026_replay] at h
  simpa only [momentPanelPhase_owner2622K00P026] using h

theorem momentScalarAmp2622K00P026_radius_le :
    (momentScalarAmp2622K00P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [momentScalarAmp2622K00P026Expected]

def momentScalarGrow2622K00P026Input : RatPair2542 := (momentPanelGrowth2622K00P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P026Expected : RatState2542 :=
  ((((3292379987893243445144808439852502115786395378381164890106604902166824536656287482510693932135849 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((521697873345170331560424140083889584317719814355 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K00P026_replay :
    compactExp2620 momentScalarGrow2622K00P026Input 20 = momentScalarGrow2622K00P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P026] using h

theorem momentScalarGrow2622K00P026_radius_le :
    (momentScalarGrow2622K00P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P026Expected]

end ConnesWeilRH.Dev
