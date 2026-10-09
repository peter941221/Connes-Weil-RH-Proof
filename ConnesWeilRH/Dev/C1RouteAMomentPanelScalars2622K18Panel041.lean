import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P041 : ℚ := ((-826832020495248608617700273277199766221 : ℚ) / 20681973072843608331299012136350515200)

def momentPanelGrowth2622K18P041 : ℚ := ((10240707422525245849823245757188270065523 : ℚ) / 19520061772722576365806994333466466713600)

theorem momentPanelPhase_owner2622K18P041 :
    (momentPanelPhase2622K18P041 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-97 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P041 :
    (momentPanelGrowth2622K18P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P041Input : RatPair2542 := (momentPanelPhase2622K18P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P041Expected : RatState2542 :=
  ((((9272646525408693024477477966410977632939812953022563790915108981550871065420355 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5877463257738865315008767045123 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K18P041_replay :
    compactExp2620 momentScalarAmp2622K18P041Input 20 = momentScalarAmp2622K18P041Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622K18P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P041]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P041 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P041_replay] at h
  simpa only [momentPanelPhase_owner2622K18P041] using h

theorem momentScalarAmp2622K18P041_radius_le :
    (momentScalarAmp2622K18P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P041Expected]

def momentScalarGrow2622K18P041Input : RatPair2542 := (momentPanelGrowth2622K18P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P041Expected : RatState2542 :=
  ((((902360866914265598787782160577863962885646030155137544797916305691664746524325828025575443706749 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2287755444519959346788635866540175069430613252389 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K18P041_replay :
    compactExp2620 momentScalarGrow2622K18P041Input 20 = momentScalarGrow2622K18P041Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P041_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P041] using h

theorem momentScalarGrow2622K18P041_radius_le :
    (momentScalarGrow2622K18P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P041Expected]

end ConnesWeilRH.Dev
