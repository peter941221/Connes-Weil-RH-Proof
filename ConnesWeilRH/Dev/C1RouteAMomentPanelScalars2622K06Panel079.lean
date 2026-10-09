import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P079 : ℚ := ((-60830739 : ℚ) / 1977950)

def momentPanelGrowth2622K06P079 : ℚ := ((87531547 : ℚ) / 813288675)

theorem momentPanelPhase_owner2622K06P079 :
    (momentPanelPhase2622K06P079 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P079 :
    (momentPanelGrowth2622K06P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P079Input : RatPair2542 := (momentPanelPhase2622K06P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P079Expected : RatState2542 :=
  ((((5874843107856916308782811908193611585182387194367628678700320334376456656119411851 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((119159469135398885232097068706528011 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P079_replay :
    compactExp2620 momentScalarAmp2622K06P079Input 20 = momentScalarAmp2622K06P079Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622K06P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P079]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P079 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P079_replay] at h
  simpa only [momentPanelPhase_owner2622K06P079] using h

theorem momentScalarAmp2622K06P079_radius_le :
    (momentScalarAmp2622K06P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P079Expected]

def momentScalarGrow2622K06P079Input : RatPair2542 := (momentPanelGrowth2622K06P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P079Expected : RatState2542 :=
  ((((2378703320286727997538132301386926108943538039572395902906100291525517479467508428370722858717781 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3015364382226969073915065770609228851968272950815 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P079_replay :
    compactExp2620 momentScalarGrow2622K06P079Input 20 = momentScalarGrow2622K06P079Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P079_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P079] using h

theorem momentScalarGrow2622K06P079_radius_le :
    (momentScalarGrow2622K06P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P079Expected]

end ConnesWeilRH.Dev
