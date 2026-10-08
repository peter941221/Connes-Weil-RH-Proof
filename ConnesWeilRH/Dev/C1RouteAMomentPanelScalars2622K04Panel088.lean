import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P088 : ℚ := ((-344160997375361879999227246899156389521823913778419771 : ℚ) / 11415412495800808320680382840850951999816484048076800)

def momentPanelGrowth2622K04P088 : ℚ := ((31703862004425961765286728909944475092634303593764509 : ℚ) / 297105442273213738772295897916602219206846301654220800)

theorem momentPanelPhase_owner2622K04P088 :
    (momentPanelPhase2622K04P088 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P088 :
    (momentPanelGrowth2622K04P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P088Input : RatPair2542 := (momentPanelPhase2622K04P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P088Expected : RatState2542 :=
  ((((172242686020533588690646528874240729073937996255779693634006428781036244457539424137 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((109174911127509492092161898020117085 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P088_replay :
    compactExp2620 momentScalarAmp2622K04P088Input 20 = momentScalarAmp2622K04P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K04P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P088_replay] at h
  simpa only [momentPanelPhase_owner2622K04P088] using h

theorem momentScalarAmp2622K04P088_radius_le :
    (momentScalarAmp2622K04P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P088Expected]

def momentScalarGrow2622K04P088Input : RatPair2542 := (momentPanelGrowth2622K04P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P088Expected : RatState2542 :=
  ((((2376521769897870870963690624227475737169260293786174126748847093147787660077197148774828788646031 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1506299470743538042532771281806731034433210299765 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P088_replay :
    compactExp2620 momentScalarGrow2622K04P088Input 20 = momentScalarGrow2622K04P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P088] using h

theorem momentScalarGrow2622K04P088_radius_le :
    (momentScalarGrow2622K04P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P088Expected]

end ConnesWeilRH.Dev
