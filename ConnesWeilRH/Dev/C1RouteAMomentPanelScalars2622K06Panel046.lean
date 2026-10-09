import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P046 : ℚ := ((-62821497 : ℚ) / 1621550)

def momentPanelGrowth2622K06P046 : ℚ := ((944047 : ℚ) / 2116800)

theorem momentPanelPhase_owner2622K06P046 :
    (momentPanelPhase2622K06P046 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P046 :
    (momentPanelGrowth2622K06P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P046Input : RatPair2542 := (momentPanelPhase2622K06P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P046Expected : RatState2542 :=
  ((((3992368824632931968974536954113110454551360248541915364521617847361404990499687 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((20244464112799862708353691637525 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P046_replay :
    compactExp2620 momentScalarAmp2622K06P046Input 20 = momentScalarAmp2622K06P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K06P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P046_replay] at h
  simpa only [momentPanelPhase_owner2622K06P046] using h

theorem momentScalarAmp2622K06P046_radius_le :
    (momentScalarAmp2622K06P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P046Expected]

def momentScalarGrow2622K06P046Input : RatPair2542 := (momentPanelGrowth2622K06P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P046Expected : RatState2542 :=
  ((((3336449492312630217302406153348150496602001395310247912321571655010488510480903049580088989460811 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((264340650168689913307883299980666475207755334101 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K06P046_replay :
    compactExp2620 momentScalarGrow2622K06P046Input 20 = momentScalarGrow2622K06P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P046] using h

theorem momentScalarGrow2622K06P046_radius_le :
    (momentScalarGrow2622K06P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P046Expected]

end ConnesWeilRH.Dev
