import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P044 : ℚ := ((-20962143 : ℚ) / 528650)

def momentPanelGrowth2622K06P044 : ℚ := ((15669947 : ℚ) / 32373675)

theorem momentPanelPhase_owner2622K06P044 :
    (momentPanelPhase2622K06P044 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P044 :
    (momentPanelGrowth2622K06P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P044Input : RatPair2542 := (momentPanelPhase2622K06P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P044Expected : RatState2542 :=
  ((((12848748265032933033577089036958867570815618339976634699967235416277765740579237 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8144170902483632121712184931945 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P044_replay :
    compactExp2620 momentScalarAmp2622K06P044Input 20 = momentScalarAmp2622K06P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K06P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P044_replay] at h
  simpa only [momentPanelPhase_owner2622K06P044] using h

theorem momentScalarAmp2622K06P044_radius_le :
    (momentScalarAmp2622K06P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P044Expected]

def momentScalarGrow2622K06P044Input : RatPair2542 := (momentPanelGrowth2622K06P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P044Expected : RatState2542 :=
  ((((433233223706607022734531500430275920605966030760094604058295586250084621264381640891367616160001 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2196752410237908995105002436292390800646700951057 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P044_replay :
    compactExp2620 momentScalarGrow2622K06P044Input 20 = momentScalarGrow2622K06P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P044] using h

theorem momentScalarGrow2622K06P044_radius_le :
    (momentScalarGrow2622K06P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P044Expected]

end ConnesWeilRH.Dev
