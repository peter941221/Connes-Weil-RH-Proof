import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P056 : ℚ := ((-823753036486883396473161503751676481151 : ℚ) / 24008288247842482280826361347257139200)

def momentPanelGrowth2622K24P056 : ℚ := ((456595378410706050102772558752121343083 : ℚ) / 1652516421300881125875750680066103705600)

theorem momentPanelPhase_owner2622K24P056 :
    (momentPanelPhase2622K24P056 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P056 :
    (momentPanelGrowth2622K24P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P056Input : RatPair2542 := (momentPanelPhase2622K24P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P056Expected : RatState2542 :=
  ((((2681861687950461835923121712759398859046331353788797584714472751869794367525967101 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((849943706371114756647380290535185 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K24P056_replay :
    compactExp2620 momentScalarAmp2622K24P056Input 20 = momentScalarAmp2622K24P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K24P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P056_replay] at h
  simpa only [momentPanelPhase_owner2622K24P056] using h

theorem momentScalarAmp2622K24P056_radius_le :
    (momentScalarAmp2622K24P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P056Expected]

def momentScalarGrow2622K24P056Input : RatPair2542 := (momentPanelGrowth2622K24P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P056Expected : RatState2542 :=
  ((((2815759226351422341306903853197765685683787719132326012284051643932099754746403901242604735829311 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((446174741604353284495650252892732060108374505159 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K24P056_replay :
    compactExp2620 momentScalarGrow2622K24P056Input 20 = momentScalarGrow2622K24P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P056] using h

theorem momentScalarGrow2622K24P056_radius_le :
    (momentScalarGrow2622K24P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P056Expected]

end ConnesWeilRH.Dev
