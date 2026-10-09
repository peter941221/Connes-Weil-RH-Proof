import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P067 : ℚ := ((-44600300259740426929091014056282317802405600434035041 : ℚ) / 1387513116941025957969623288060021191785850957987840)

def momentPanelGrowth2622K00P067 : ℚ := ((12156358470887617884133182480117523439217998794224087037 : ℚ) / 68279408588448779244430487035813638007363033235246284800)

theorem momentPanelPhase_owner2622K00P067 :
    (momentPanelPhase2622K00P067 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P067 :
    (momentPanelGrowth2622K00P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P067Input : RatPair2542 := (momentPanelPhase2622K00P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P067Expected : RatState2542 :=
  ((((2927670442940443142102573693099531868410869461310779433103972175226140950255507071 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1855688482469709268063496754954975 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K00P067_replay :
    compactExp2620 momentScalarAmp2622K00P067Input 20 = momentScalarAmp2622K00P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K00P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P067_replay] at h
  simpa only [momentPanelPhase_owner2622K00P067] using h

theorem momentScalarAmp2622K00P067_radius_le :
    (momentScalarAmp2622K00P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P067Expected]

def momentScalarGrow2622K00P067Input : RatPair2542 := (momentPanelGrowth2622K00P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P067Expected : RatState2542 :=
  ((((2552229467837874337911675755537386502513999701009156588639113524620227424373908447552563744944871 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1617667333747576574937550636156106939262544474135 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P067_replay :
    compactExp2620 momentScalarGrow2622K00P067Input 20 = momentScalarGrow2622K00P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P067] using h

theorem momentScalarGrow2622K00P067_radius_le :
    (momentScalarGrow2622K00P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P067Expected]

end ConnesWeilRH.Dev
