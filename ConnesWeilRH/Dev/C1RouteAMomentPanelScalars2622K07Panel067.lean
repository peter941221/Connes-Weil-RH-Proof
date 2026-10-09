import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P067 : ℚ := ((-4118088088101987881456838498062828625 : ℚ) / 123235920751787549495903498813833216)

def momentPanelGrowth2622K07P067 : ℚ := ((284521727957682639347957280540389878025 : ℚ) / 1212885944362951904274980688495120482304)

theorem momentPanelPhase_owner2622K07P067 :
    (momentPanelPhase2622K07P067 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P067 :
    (momentPanelGrowth2622K07P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P067Input : RatPair2542 := (momentPanelPhase2622K07P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P067Expected : RatState2542 :=
  ((((6562742488106564452337945234366416085930007010977742949920439059093483389250179767 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4159764790674443402145763667256647 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P067_replay :
    compactExp2620 momentScalarAmp2622K07P067Input 20 = momentScalarAmp2622K07P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K07P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P067_replay] at h
  simpa only [momentPanelPhase_owner2622K07P067] using h

theorem momentScalarAmp2622K07P067_radius_le :
    (momentScalarAmp2622K07P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P067Expected]

def momentScalarGrow2622K07P067Input : RatPair2542 := (momentPanelGrowth2622K07P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P067Expected : RatState2542 :=
  ((((2700700755215661874081555681644230188574294604015942314646628707033129597498285898525368386578933 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1711772083743445843816484117429917402891310550749 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P067_replay :
    compactExp2620 momentScalarGrow2622K07P067Input 20 = momentScalarGrow2622K07P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P067] using h

theorem momentScalarGrow2622K07P067_radius_le :
    (momentScalarGrow2622K07P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P067Expected]

end ConnesWeilRH.Dev
