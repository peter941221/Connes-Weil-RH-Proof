import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P004 : ℚ := ((-103380950951903984555870300580497018175 : ℚ) / 872873779702753288364993906344984576)

def momentPanelGrowth2622K07P004 : ℚ := ((44069835899199550208941787183973097025 : ℚ) / 5730470314958121051559512694843244544)

theorem momentPanelPhase_owner2622K07P004 :
    (momentPanelPhase2622K07P004 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P004 :
    (momentPanelGrowth2622K07P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P004Input : RatPair2542 := (momentPanelPhase2622K07P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P004Expected : RatState2542 :=
  ((((781383949795017474226699769390792281765968353 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P004_replay :
    compactExp2620 momentScalarAmp2622K07P004Input 20 = momentScalarAmp2622K07P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K07P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P004_replay] at h
  simpa only [momentPanelPhase_owner2622K07P004] using h

theorem momentScalarAmp2622K07P004_radius_le :
    (momentScalarAmp2622K07P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P004Expected]

def momentScalarGrow2622K07P004Input : RatPair2542 := (momentPanelGrowth2622K07P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P004Expected : RatState2542 :=
  ((((4672121184556578607614601458277967229043183981916423210250745395492913094379346393427552348752647477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((740321723323978822674587868534926645028923311948363 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P004_replay :
    compactExp2620 momentScalarGrow2622K07P004Input 20 = momentScalarGrow2622K07P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P004] using h

theorem momentScalarGrow2622K07P004_radius_le :
    (momentScalarGrow2622K07P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P004Expected]

end ConnesWeilRH.Dev
