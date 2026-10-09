import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P039 : ℚ := ((-825653920692546854629709384303940140737 : ℚ) / 20146517459307204232106804702399692800)

def momentPanelGrowth2622K05P039 : ℚ := ((31815559948655315569469870628164660663889 : ℚ) / 55518229525812051567237374252522720460800)

theorem momentPanelPhase_owner2622K05P039 :
    (momentPanelPhase2622K05P039 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P039 :
    (momentPanelGrowth2622K05P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P039Input : RatPair2542 := (momentPanelPhase2622K05P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P039Expected : RatState2542 :=
  ((((3397353730362391516945863594833280010703307740276557365274467590786214505944655 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1076707059423183028788961479223 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P039_replay :
    compactExp2620 momentScalarAmp2622K05P039Input 20 = momentScalarAmp2622K05P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K05P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P039_replay] at h
  simpa only [momentPanelPhase_owner2622K05P039] using h

theorem momentScalarAmp2622K05P039_radius_le :
    (momentScalarAmp2622K05P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P039Expected]

def momentScalarGrow2622K05P039Input : RatPair2542 := (momentPanelGrowth2622K05P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P039Expected : RatState2542 :=
  ((((3788590140293574641412079972434044168018432246708897603556984956521560458537943175339315352072689 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2401302970326566271099780690913701189728925427545 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P039_replay :
    compactExp2620 momentScalarGrow2622K05P039Input 20 = momentScalarGrow2622K05P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P039] using h

theorem momentScalarGrow2622K05P039_radius_le :
    (momentScalarGrow2622K05P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P039Expected]

end ConnesWeilRH.Dev
