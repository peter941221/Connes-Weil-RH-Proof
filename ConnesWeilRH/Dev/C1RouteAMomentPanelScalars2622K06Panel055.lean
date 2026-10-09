import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P055 : ℚ := ((-62431491 : ℚ) / 1761950)

def momentPanelGrowth2622K06P055 : ℚ := ((321067 : ℚ) / 1026675)

theorem momentPanelPhase_owner2622K06P055 :
    (momentPanelPhase2622K06P055 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P055 :
    (momentPanelGrowth2622K06P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P055Input : RatPair2542 := (momentPanelPhase2622K06P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P055Expected : RatState2542 :=
  ((((873301458911134070410948218769842097137278565818137975696870857354791890145577525 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((553539265217524584430223150044855 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P055_replay :
    compactExp2620 momentScalarAmp2622K06P055Input 20 = momentScalarAmp2622K06P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K06P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P055_replay] at h
  simpa only [momentPanelPhase_owner2622K06P055] using h

theorem momentScalarAmp2622K06P055_radius_le :
    (momentScalarAmp2622K06P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P055Expected]

def momentScalarGrow2622K06P055Input : RatPair2542 := (momentPanelGrowth2622K06P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P055Expected : RatState2542 :=
  ((((730051316805974977643722346885690338686824022764424431475332479260778365879521506959199534945111 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1850899427884645865127975834617921046236879700959 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P055_replay :
    compactExp2620 momentScalarGrow2622K06P055Input 20 = momentScalarGrow2622K06P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P055] using h

theorem momentScalarGrow2622K06P055_radius_le :
    (momentScalarGrow2622K06P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P055Expected]

end ConnesWeilRH.Dev
