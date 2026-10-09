import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P138 : ℚ := ((-29212482596505016094031145182393262825 : ℚ) / 827278922913744333251960485454020608)

def momentPanelGrowth2622K07P138 : ℚ := ((460574096522873928640091282781527322025 : ℚ) / 780802470908903054632279773338658668544)

theorem momentPanelPhase_owner2622K07P138 :
    (momentPanelPhase2622K07P138 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P138 :
    (momentPanelGrowth2622K07P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P138Input : RatPair2542 := (momentPanelPhase2622K07P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P138Expected : RatState2542 :=
  ((((123284080600044130722902373206381263135391226858444038196793774025232435874448013 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((625145608153442958924058015282105 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P138_replay :
    compactExp2620 momentScalarAmp2622K07P138Input 20 = momentScalarAmp2622K07P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K07P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P138_replay] at h
  simpa only [momentPanelPhase_owner2622K07P138] using h

theorem momentScalarAmp2622K07P138_radius_le :
    (momentScalarAmp2622K07P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P138Expected]

def momentScalarGrow2622K07P138Input : RatPair2542 := (momentPanelGrowth2622K07P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P138Expected : RatState2542 :=
  ((((481600693352342063564120443853951453967815491918138296613469378610895633105454992343613663346001 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4884008516504819260416716422674874303841292020269 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P138_replay :
    compactExp2620 momentScalarGrow2622K07P138Input 20 = momentScalarGrow2622K07P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P138] using h

theorem momentScalarGrow2622K07P138_radius_le :
    (momentScalarGrow2622K07P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P138Expected]

end ConnesWeilRH.Dev
