import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P001 : ℚ := ((-61534767 : ℚ) / 433550)

def momentPanelGrowth2622K06P001 : ℚ := ((446440747 : ℚ) / 36018675)

theorem momentPanelPhase_owner2622K06P001 :
    (momentPanelPhase2622K06P001 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-177 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P001, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P001 :
    (momentPanelGrowth2622K06P001 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P001, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P001Input : RatPair2542 := (momentPanelPhase2622K06P001 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P001Expected : RatState2542 :=
  ((((3055241675707658411179203157974919 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P001_replay :
    compactExp2620 momentScalarAmp2622K06P001Input 20 = momentScalarAmp2622K06P001Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P001_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-177 / 200) 0) -
      (momentScalarAmp2622K06P001Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P001]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P001 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P001 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P001Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P001_replay] at h
  simpa only [momentPanelPhase_owner2622K06P001] using h

theorem momentScalarAmp2622K06P001_radius_le :
    (momentScalarAmp2622K06P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P001Expected]

def momentScalarGrow2622K06P001Input : RatPair2542 := (momentPanelGrowth2622K06P001 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P001Expected : RatState2542 :=
  ((((128970193696016259642678370602366550153696917096424493383298726942004797994697369034422247968907482557 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((653948843747304494996730871178387045489690144670951577 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P001_replay :
    compactExp2620 momentScalarGrow2622K06P001Input 20 = momentScalarGrow2622K06P001Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P001_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P001Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P001]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P001 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P001 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P001Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P001_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P001] using h

theorem momentScalarGrow2622K06P001_radius_le :
    (momentScalarGrow2622K06P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P001Expected]

end ConnesWeilRH.Dev
