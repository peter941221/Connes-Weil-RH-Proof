import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P132 : ℚ := ((-6384052661589369775468882558661969819 : ℚ) / 177268259935915599505298976239779840)

def momentPanelGrowth2622K05P132 : ℚ := ((9038377296597822861144075806522219664763 : ℚ) / 22458982924291703410236951044810185113600)

theorem momentPanelPhase_owner2622K05P132 :
    (momentPanelPhase2622K05P132 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P132 :
    (momentPanelGrowth2622K05P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P132Input : RatPair2542 := (momentPanelPhase2622K05P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P132Expected : RatState2542 :=
  ((((488797461461300201304966760911470674894908642705541682029182592313087233378348639 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((309822839647417286473069721220651 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P132_replay :
    compactExp2620 momentScalarAmp2622K05P132Input 20 = momentScalarAmp2622K05P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K05P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P132_replay] at h
  simpa only [momentPanelPhase_owner2622K05P132] using h

theorem momentScalarAmp2622K05P132_radius_le :
    (momentScalarAmp2622K05P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P132Expected]

def momentScalarGrow2622K05P132Input : RatPair2542 := (momentPanelGrowth2622K05P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P132Expected : RatState2542 :=
  ((((3194300565826938125314292574009769701987369101706184456289660447528517935500966313472210734188641 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((126539233609107870976182814925531379531559798853 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P132_replay :
    compactExp2620 momentScalarGrow2622K05P132Input 20 = momentScalarGrow2622K05P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P132] using h

theorem momentScalarGrow2622K05P132_radius_le :
    (momentScalarGrow2622K05P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P132Expected]

end ConnesWeilRH.Dev
