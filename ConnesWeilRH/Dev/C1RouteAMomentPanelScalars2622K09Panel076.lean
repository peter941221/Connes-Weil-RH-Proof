import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P076 : ℚ := ((-2450543231338357450544439498233536961973 : ℚ) / 79651050754500474921883250525313433600)

def momentPanelGrowth2622K09P076 : ℚ := ((208923228450046598010477673337989365323 : ℚ) / 2030742795589777475941519022047730073600)

theorem momentPanelPhase_owner2622K09P076 :
    (momentPanelPhase2622K09P076 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P076 :
    (momentPanelGrowth2622K09P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P076Input : RatPair2542 := (momentPanelPhase2622K09P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P076Expected : RatState2542 :=
  ((((92918034344450606812686466769809721217038457960130098786503883321535051782119364993 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((58895529018181505785863749199810411 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K09P076_replay :
    compactExp2620 momentScalarAmp2622K09P076Input 20 = momentScalarAmp2622K09P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K09P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P076_replay] at h
  simpa only [momentPanelPhase_owner2622K09P076] using h

theorem momentScalarAmp2622K09P076_radius_le :
    (momentScalarAmp2622K09P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P076Expected]

def momentScalarGrow2622K09P076Input : RatPair2542 := (momentPanelGrowth2622K09P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P076Expected : RatState2542 :=
  ((((1183719823513704095443716150230899619447057790624690219954424087876773942813004347802755231328755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3001085995109217467983165447977104454820280413209 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P076_replay :
    compactExp2620 momentScalarGrow2622K09P076Input 20 = momentScalarGrow2622K09P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P076] using h

theorem momentScalarGrow2622K09P076_radius_le :
    (momentScalarGrow2622K09P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P076Expected]

end ConnesWeilRH.Dev
