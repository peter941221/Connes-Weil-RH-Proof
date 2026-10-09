import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P036 : ℚ := ((-35786892089903573059620355973250387925 : ℚ) / 772110768791811789698823961956057088)

def momentPanelGrowth2622K07P036 : ℚ := ((92415732527659018656566561808520179075 : ℚ) / 127229162119373697672311081541526618112)

theorem momentPanelPhase_owner2622K07P036 :
    (momentPanelPhase2622K07P036 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-107 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P036 :
    (momentPanelGrowth2622K07P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P036Input : RatPair2542 := (momentPanelPhase2622K07P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P036Expected : RatState2542 :=
  ((((1982476411580769712201233431189198757140505794468352638205862622575104904659 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((20108005849027189736743856133 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P036_replay :
    compactExp2620 momentScalarAmp2622K07P036Input 20 = momentScalarAmp2622K07P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K07P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P036_replay] at h
  simpa only [momentPanelPhase_owner2622K07P036] using h

theorem momentScalarAmp2622K07P036_radius_le :
    (momentScalarAmp2622K07P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P036Expected]

def momentScalarGrow2622K07P036Input : RatPair2542 := (momentPanelGrowth2622K07P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P036Expected : RatState2542 :=
  ((((276018434931151084779100460001030593016664687464852688979660007605820948748375598806020082585055 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2799157538676001260324431283162793137719488917455 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P036_replay :
    compactExp2620 momentScalarGrow2622K07P036Input 20 = momentScalarGrow2622K07P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P036] using h

theorem momentScalarGrow2622K07P036_radius_le :
    (momentScalarGrow2622K07P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P036Expected]

end ConnesWeilRH.Dev
