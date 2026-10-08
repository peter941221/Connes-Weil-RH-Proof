import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P142 : ℚ := ((-2411350445725423996674521717731847689761557372911347 : ℚ) / 66167203033848300085862137543678594522704133488640)

def momentPanelGrowth2622K04P142 : ℚ := ((1745854941633279812475454930641055672262753956079013829 : ℚ) / 2460122156532179233874225217192823290317080934272204800)

theorem momentPanelPhase_owner2622K04P142 :
    (momentPanelPhase2622K04P142 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P142 :
    (momentPanelGrowth2622K04P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P142Input : RatPair2542 := (momentPanelPhase2622K04P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P142Expected : RatState2542 :=
  ((((318038480542757736683447559184086121234642325114478265105976928071270354240684479 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((201587842656082659153721399752611 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P142_replay :
    compactExp2620 momentScalarAmp2622K04P142Input 20 = momentScalarAmp2622K04P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K04P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P142_replay] at h
  simpa only [momentPanelPhase_owner2622K04P142] using h

theorem momentScalarAmp2622K04P142_radius_le :
    (momentScalarAmp2622K04P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P142Expected]

def momentScalarGrow2622K04P142Input : RatPair2542 := (momentPanelGrowth2622K04P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P142Expected : RatState2542 :=
  ((((4343110266591526653653482225970691016456655382153376796979433689350651274074060121376385863532355 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2752771305112478738220633594768691154883292119589 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P142_replay :
    compactExp2620 momentScalarGrow2622K04P142Input 20 = momentScalarGrow2622K04P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P142] using h

theorem momentScalarGrow2622K04P142_radius_le :
    (momentScalarGrow2622K04P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P142Expected]

end ConnesWeilRH.Dev
