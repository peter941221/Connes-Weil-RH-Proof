import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P144 : ℚ := ((-29105886554110899726163407145053533725 : ℚ) / 760428100860108427534630345215311872)

def momentPanelGrowth2622K07P144 : ℚ := ((798918313194174088251448801825891225 : ℚ) / 1052535363971899784980318658236514304)

theorem momentPanelPhase_owner2622K07P144 :
    (momentPanelPhase2622K07P144 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (109 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P144 :
    (momentPanelGrowth2622K07P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P144Input : RatPair2542 := (momentPanelPhase2622K07P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P144Expected : RatState2542 :=
  ((((50896883538282814219437562193061925878941058362135714283377510821023452616620221 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((64521822550480553274231059451011 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P144_replay :
    compactExp2620 momentScalarAmp2622K07P144Input 20 = momentScalarAmp2622K07P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K07P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P144_replay] at h
  simpa only [momentPanelPhase_owner2622K07P144] using h

theorem momentScalarAmp2622K07P144_radius_le :
    (momentScalarAmp2622K07P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P144Expected]

def momentScalarGrow2622K07P144Input : RatPair2542 := (momentPanelGrowth2622K07P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P144Expected : RatState2542 :=
  ((((4562955862177510598026555677392005451384503182880955733346825993170844723927255988421764221888303 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((723028693802807187800591908033803964861907508321 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P144_replay :
    compactExp2620 momentScalarGrow2622K07P144Input 20 = momentScalarGrow2622K07P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P144] using h

theorem momentScalarGrow2622K07P144_radius_le :
    (momentScalarGrow2622K07P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P144Expected]

end ConnesWeilRH.Dev
