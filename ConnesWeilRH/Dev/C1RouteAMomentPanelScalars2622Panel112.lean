import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P112 : ℚ := ((-43089797980113748163130075906694663376950352144524959 : ℚ) / 1387513116941025957969623288060021191785850957987840)

def momentPanelGrowth2622P112 : ℚ := ((12156358470887617884133182480117523439217998794224087037 : ℚ) / 68279408588448779244430487035813638007363033235246284800)

theorem momentPanelPhase_owner2622P112 :
    (momentPanelPhase2622P112 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 40) 0 := by
  norm_num [momentPanelPhase2622P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P112 :
    (momentPanelGrowth2622P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P112Input : RatPair2542 := (momentPanelPhase2622P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P112Expected : RatState2542 :=
  ((((17391719752873807139426865400953175624504050652369172604921137800693260665860186441 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((44094553886856219835613792946875821 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P112_replay :
    compactExp2620 momentScalarAmp2622P112Input 20 = momentScalarAmp2622P112Expected := by
  decide +kernel

theorem momentScalarAmp2622P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P112]
  have h := compactExp_real_error2620 momentPanelPhase2622P112 20 hsmall
  change |Real.exp (momentPanelPhase2622P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P112_replay] at h
  simpa only [momentPanelPhase_owner2622P112] using h

theorem momentScalarAmp2622P112_radius_le :
    (momentScalarAmp2622P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P112Expected]

def momentScalarGrow2622P112Input : RatPair2542 := (momentPanelGrowth2622P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P112Expected : RatState2542 :=
  ((((2552229467837874337911675755537386502513999701009156588639113524620227424373908447552563744944871 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1617667333747576574937550636156106939262544474135 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P112_replay :
    compactExp2620 momentScalarGrow2622P112Input 20 = momentScalarGrow2622P112Expected := by
  decide +kernel

theorem momentScalarGrow2622P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P112_replay] at h
  simpa only [momentPanelGrowth_owner2622P112] using h

theorem momentScalarGrow2622P112_radius_le :
    (momentScalarGrow2622P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P112Expected]

end ConnesWeilRH.Dev
