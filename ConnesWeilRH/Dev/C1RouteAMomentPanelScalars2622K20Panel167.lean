import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P167 : ℚ := ((-6386659746293895471283232153722588493 : ℚ) / 86403064911556116006015290478428160)

def momentPanelGrowth2622K20P167 : ℚ := ((2981356347869064514102213485086354629729 : ℚ) / 971974647146675532639921373491023052800)

theorem momentPanelPhase_owner2622K20P167 :
    (momentPanelPhase2622K20P167 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (31 / 40) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P167 :
    (momentPanelGrowth2622K20P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P167Input : RatPair2542 := (momentPanelPhase2622K20P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P167Expected : RatState2542 :=
  ((((16897843809266626391461759567537672952444355889590051915624396559 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851660651330675353517 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P167_replay :
    compactExp2620 momentScalarAmp2622K20P167Input 20 = momentScalarAmp2622K20P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K20P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P167_replay] at h
  simpa only [momentPanelPhase_owner2622K20P167] using h

theorem momentScalarAmp2622K20P167_radius_le :
    (momentScalarAmp2622K20P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P167Expected]

def momentScalarGrow2622K20P167Input : RatPair2542 := (momentPanelGrowth2622K20P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P167Expected : RatState2542 :=
  ((((22945015368731237109241161359221367051406572949175218339499895733801240197367923501232353026204877 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((58172354841453999861835257184954277197533207796043 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P167_replay :
    compactExp2620 momentScalarGrow2622K20P167Input 20 = momentScalarGrow2622K20P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P167] using h

theorem momentScalarGrow2622K20P167_radius_le :
    (momentScalarGrow2622K20P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P167Expected]

end ConnesWeilRH.Dev
