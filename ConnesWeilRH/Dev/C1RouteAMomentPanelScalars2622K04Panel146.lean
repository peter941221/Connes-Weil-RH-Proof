import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P146 : ℚ := ((-100316474402923122189631563379973169986215010604677573 : ℚ) / 2591025461338399568073212348938613470589238221209600)

def momentPanelGrowth2622K04P146 : ℚ := ((5497190841035791605112877623956840265122774986826730527 : ℚ) / 6504824227001452024507232240191615978527519651817062400)

theorem momentPanelPhase_owner2622K04P146 :
    (momentPanelPhase2622K04P146 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P146 :
    (momentPanelGrowth2622K04P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P146Input : RatPair2542 := (momentPanelPhase2622K04P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P146Expected : RatState2542 :=
  ((((16369389021992376960921456251646186165774639547221730894107564066676320056907351 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((20751433225506453291724275499873 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P146_replay :
    compactExp2620 momentScalarAmp2622K04P146Input 20 = momentScalarAmp2622K04P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K04P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P146_replay] at h
  simpa only [momentPanelPhase_owner2622K04P146] using h

theorem momentScalarAmp2622K04P146_radius_le :
    (momentScalarAmp2622K04P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P146Expected]

def momentScalarGrow2622K04P146Input : RatPair2542 := (momentPanelGrowth2622K04P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P146Expected : RatState2542 :=
  ((((4973000100775648229227876385833740523291450607420144809741432238819966628956662597193550920075551 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3152010740993736654881858203873702989190956520381 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P146_replay :
    compactExp2620 momentScalarGrow2622K04P146Input 20 = momentScalarGrow2622K04P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P146] using h

theorem momentScalarGrow2622K04P146_radius_le :
    (momentScalarGrow2622K04P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P146Expected]

end ConnesWeilRH.Dev
