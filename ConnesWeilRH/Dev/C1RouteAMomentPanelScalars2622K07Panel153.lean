import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P153 : ℚ := ((-29142298462656364448356890968918075575 : ℚ) / 645548532865025366253393113931317248)

def momentPanelGrowth2622K07P153 : ℚ := ((2176885257284847501667584484037826025 : ℚ) / 1841115449361876731063387788236816384)

theorem momentPanelPhase_owner2622K07P153 :
    (momentPanelPhase2622K07P153 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (127 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P153, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P153 :
    (momentPanelGrowth2622K07P153 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P153, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P153Input : RatPair2542 := (momentPanelPhase2622K07P153 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P153Expected : RatState2542 :=
  ((((52971258132332048110767919458899220183291758349570058647415260192049725168271 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((67154355991983974823023251003 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P153_replay :
    compactExp2620 momentScalarAmp2622K07P153Input 20 = momentScalarAmp2622K07P153Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P153_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (127 / 200) 0) -
      (momentScalarAmp2622K07P153Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P153]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P153 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P153 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P153Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P153_replay] at h
  simpa only [momentPanelPhase_owner2622K07P153] using h

theorem momentScalarAmp2622K07P153_radius_le :
    (momentScalarAmp2622K07P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P153Expected]

def momentScalarGrow2622K07P153Input : RatPair2542 := (momentPanelGrowth2622K07P153 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P153Expected : RatState2542 :=
  ((((3483908179813025021614618784314406627184387362236548902403721387304098568132824558851638096472291 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((276023332211249319181461897146201463804552515687 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P153_replay :
    compactExp2620 momentScalarGrow2622K07P153Input 20 = momentScalarGrow2622K07P153Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P153_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P153Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P153]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P153 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P153 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P153Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P153_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P153] using h

theorem momentScalarGrow2622K07P153_radius_le :
    (momentScalarGrow2622K07P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P153Expected]

end ConnesWeilRH.Dev
