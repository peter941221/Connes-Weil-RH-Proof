import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P006 : ℚ := ((-73257384609604903258919414463889510816131863640278075 : ℚ) / 737510263738106885098534458709454318793874959499264)

def momentPanelGrowth2622K03P006 : ℚ := ((281132434821910563176978606488310881412448345576825 : ℚ) / 48320897884252977733109329781682107337374269702144)

theorem momentPanelPhase_owner2622K03P006 :
    (momentPanelPhase2622K03P006 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-167 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P006, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P006 :
    (momentPanelGrowth2622K03P006 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P006, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P006Input : RatPair2542 := (momentPanelPhase2622K03P006 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P006Expected : RatState2542 :=
  ((((155181203107216804210805196111800236583227104191573755 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629174805195 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P006_replay :
    compactExp2620 momentScalarAmp2622K03P006Input 20 = momentScalarAmp2622K03P006Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P006_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-167 / 200) 0) -
      (momentScalarAmp2622K03P006Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P006]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P006 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P006 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P006Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P006_replay] at h
  simpa only [momentPanelPhase_owner2622K03P006] using h

theorem momentScalarAmp2622K03P006_radius_le :
    (momentScalarAmp2622K03P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P006Expected]

def momentScalarGrow2622K03P006Input : RatPair2542 := (momentPanelGrowth2622K03P006 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P006Expected : RatState2542 :=
  ((((718351410331987345079592339863512817421403853597032158788440039352272950491672297109674036258993373 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((56913346495223985612872055646554668711305596984327 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K03P006_replay :
    compactExp2620 momentScalarGrow2622K03P006Input 20 = momentScalarGrow2622K03P006Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P006_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P006Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P006]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P006 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P006 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P006Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P006_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P006] using h

theorem momentScalarGrow2622K03P006_radius_le :
    (momentScalarGrow2622K03P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P006Expected]

end ConnesWeilRH.Dev
