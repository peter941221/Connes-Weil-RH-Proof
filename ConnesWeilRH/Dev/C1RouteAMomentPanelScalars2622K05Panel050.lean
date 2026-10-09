import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P050 : ℚ := ((-824018915543903260984110932596011286843 : ℚ) / 22823795526989224728067841872153804800)

def momentPanelGrowth2622K05P050 : ℚ := ((52809780436930659401980520780780083 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K05P050 :
    (momentPanelPhase2622K05P050 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-79 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P050, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P050 :
    (momentPanelGrowth2622K05P050 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P050, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P050Input : RatPair2542 := (momentPanelPhase2622K05P050 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P050Expected : RatState2542 :=
  ((((446732474257425857440031777680168766764611567810036835810649352077656099903663637 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((283160095087904546851466120523649 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P050_replay :
    compactExp2620 momentScalarAmp2622K05P050Input 20 = momentScalarAmp2622K05P050Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P050_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-79 / 200) 0) -
      (momentScalarAmp2622K05P050Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P050]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P050 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P050 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P050Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P050_replay] at h
  simpa only [momentPanelPhase_owner2622K05P050] using h

theorem momentScalarAmp2622K05P050_radius_le :
    (momentScalarAmp2622K05P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P050Expected]

def momentScalarGrow2622K05P050Input : RatPair2542 := (momentPanelGrowth2622K05P050 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P050Expected : RatState2542 :=
  ((((3044013595071450412598226307601181677699116338406098661301399670571734782259984435014532419399885 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1929372178633665371332211544433976969017385846799 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P050_replay :
    compactExp2620 momentScalarGrow2622K05P050Input 20 = momentScalarGrow2622K05P050Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P050_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P050Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P050]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P050 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P050 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P050Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P050_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P050] using h

theorem momentScalarGrow2622K05P050_radius_le :
    (momentScalarGrow2622K05P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P050Expected]

end ConnesWeilRH.Dev
