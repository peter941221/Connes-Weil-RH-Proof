import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P068 : ℚ := ((-20546831 : ℚ) / 635850)

def momentPanelGrowth2622K06P068 : ℚ := ((8761547 : ℚ) / 47163675)

theorem momentPanelPhase_owner2622K06P068 :
    (momentPanelPhase2622K06P068 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-43 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P068 :
    (momentPanelGrowth2622K06P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P068Input : RatPair2542 := (momentPanelPhase2622K06P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P068Expected : RatState2542 :=
  ((((19761705109076701898874194013666993094950474043471173953487571555192861447434073177 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((25051709351928705401107018348245701 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P068_replay :
    compactExp2620 momentScalarAmp2622K06P068Input 20 = momentScalarAmp2622K06P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K06P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P068_replay] at h
  simpa only [momentPanelPhase_owner2622K06P068] using h

theorem momentScalarAmp2622K06P068_radius_le :
    (momentScalarAmp2622K06P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P068Expected]

def momentScalarGrow2622K06P068Input : RatPair2542 := (momentPanelGrowth2622K06P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P068Expected : RatState2542 :=
  ((((2572036030019578781569570314342896098532328351092943491117329016935368344720913500855662238537717 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1630221219816423237025680429111404274156490492677 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P068_replay :
    compactExp2620 momentScalarGrow2622K06P068Input 20 = momentScalarGrow2622K06P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P068] using h

theorem momentScalarGrow2622K06P068_radius_le :
    (momentScalarGrow2622K06P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P068Expected]

end ConnesWeilRH.Dev
