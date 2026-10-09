import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P023 : ℚ := ((-20989121 : ℚ) / 371850)

def momentPanelGrowth2622K06P023 : ℚ := ((345123707 : ℚ) / 253092675)

theorem momentPanelPhase_owner2622K06P023 :
    (momentPanelPhase2622K06P023 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-133 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P023, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P023 :
    (momentPanelGrowth2622K06P023 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P023, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P023Input : RatPair2542 := (momentPanelPhase2622K06P023 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P023Expected : RatState2542 :=
  ((((654320930556601036535178146491682974244717318064205942104218256238503485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3247346610329750377119125 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P023_replay :
    compactExp2620 momentScalarAmp2622K06P023Input 20 = momentScalarAmp2622K06P023Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P023_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-133 / 200) 0) -
      (momentScalarAmp2622K06P023Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P023]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P023 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P023 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P023Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P023_replay] at h
  simpa only [momentPanelPhase_owner2622K06P023] using h

theorem momentScalarAmp2622K06P023_radius_le :
    (momentScalarAmp2622K06P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P023Expected]

def momentScalarGrow2622K06P023Input : RatPair2542 := (momentPanelGrowth2622K06P023 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P023Expected : RatState2542 :=
  ((((522028002218045743258107256670898246112513899196628282167219923850327633256850378069787157443235 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((5293985998186559606768515197041279580984482649753 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P023_replay :
    compactExp2620 momentScalarGrow2622K06P023Input 20 = momentScalarGrow2622K06P023Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P023_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P023Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P023]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P023 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P023 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P023Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P023_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P023] using h

theorem momentScalarGrow2622K06P023_radius_le :
    (momentScalarGrow2622K06P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P023Expected]

end ConnesWeilRH.Dev
