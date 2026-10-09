import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P051 : ℚ := ((-823811430777302812647417426014935778521 : ℚ) / 23034732586867202100476893285528371200)

def momentPanelGrowth2622K05P051 : ℚ := ((24759305553418826520975019448814728697249 : ℚ) / 72908610908898237608774834872168271052800)

theorem momentPanelPhase_owner2622K05P051 :
    (momentPanelPhase2622K05P051 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-77 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P051, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P051 :
    (momentPanelGrowth2622K05P051 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P051, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P051Input : RatPair2542 := (momentPanelPhase2622K05P051 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P051Expected : RatState2542 :=
  ((((627397125074102192408329812975670025579235958417542743043684739867037848849658185 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((99418433891030055693111573473161 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P051_replay :
    compactExp2620 momentScalarAmp2622K05P051Input 20 = momentScalarAmp2622K05P051Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P051_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-77 / 200) 0) -
      (momentScalarAmp2622K05P051Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P051]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P051 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P051 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P051Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P051_replay] at h
  simpa only [momentPanelPhase_owner2622K05P051] using h

theorem momentScalarAmp2622K05P051_radius_le :
    (momentScalarAmp2622K05P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P051Expected]

def momentScalarGrow2622K05P051Input : RatPair2542 := (momentPanelGrowth2622K05P051 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P051Expected : RatState2542 :=
  ((((2999730826558050060474131267775654156271766989261743699411848499307472002350809517396916962963735 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1901304675644667486606188767231800613675101228857 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P051_replay :
    compactExp2620 momentScalarGrow2622K05P051Input 20 = momentScalarGrow2622K05P051Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P051_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P051Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P051]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P051 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P051 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P051Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P051_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P051] using h

theorem momentScalarGrow2622K05P051_radius_le :
    (momentScalarGrow2622K05P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P051Expected]

end ConnesWeilRH.Dev
