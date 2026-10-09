import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P092 : ℚ := ((-1289346229719723863001878049691334125 : ℚ) / 43242097274985361343855539741786112)

def momentPanelGrowth2622K07P092 : ℚ := ((399931556779737194673543525240226092075 : ℚ) / 4049183539023375275007437926194942574592)

theorem momentPanelPhase_owner2622K07P092 :
    (momentPanelPhase2622K07P092 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (1 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P092, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P092 :
    (momentPanelGrowth2622K07P092 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P092, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P092Input : RatPair2542 := (momentPanelPhase2622K07P092 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P092Expected : RatState2542 :=
  ((((240034705847686419494666840803375520533211132966310404593262372152822279115710387459 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((304288791467054551435546886539141421 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P092_replay :
    compactExp2620 momentScalarAmp2622K07P092Input 20 = momentScalarAmp2622K07P092Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P092_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (1 / 40) 0) -
      (momentScalarAmp2622K07P092Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P092]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P092 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P092 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P092Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P092_replay] at h
  simpa only [momentPanelPhase_owner2622K07P092] using h

theorem momentScalarAmp2622K07P092_radius_le :
    (momentScalarAmp2622K07P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P092Expected]

def momentScalarGrow2622K07P092Input : RatPair2542 := (momentPanelGrowth2622K07P092 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P092Expected : RatState2542 :=
  ((((2357725293514298556587049076368205240041695522782073204470622071710864971133455191707727680351833 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((747192900493879260667626375560602868153213832795 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P092_replay :
    compactExp2620 momentScalarGrow2622K07P092Input 20 = momentScalarGrow2622K07P092Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P092_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P092Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P092]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P092 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P092 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P092Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P092_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P092] using h

theorem momentScalarGrow2622K07P092_radius_le :
    (momentScalarGrow2622K07P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P092Expected]

end ConnesWeilRH.Dev
