import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P089 : ℚ := ((-28545839715099997394336657894957866422084029768867909 : ℚ) / 951474674342428154707506341533505932669558036889600)

def momentPanelGrowth2622K01P089 : ℚ := ((9350503363807863917659363985988847640833740372952091 : ℚ) / 1189135214533246346784727602365387443208684532085555200)

theorem momentPanelPhase_owner2622K01P089 :
    (momentPanelPhase2622K01P089 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P089 :
    (momentPanelGrowth2622K01P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P089Input : RatPair2542 := (momentPanelPhase2622K01P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P089Expected : RatState2542 :=
  ((((12471368108646545528710987773757351182544815272079021567384242253545768400026635663 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3952447402331962714896763383775487 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K01P089_replay :
    compactExp2620 momentScalarAmp2622K01P089Input 20 = momentScalarAmp2622K01P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K01P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P089_replay] at h
  simpa only [momentPanelPhase_owner2622K01P089] using h

theorem momentScalarAmp2622K01P089_radius_le :
    (momentScalarAmp2622K01P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P089Expected]

def momentScalarGrow2622K01P089Input : RatPair2542 := (momentPanelGrowth2622K01P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P089Expected : RatState2542 :=
  ((((2152849109165028281813788613120633506484013341110518761928950230463142745474646254207733281157389 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2729060444968609972974587245797306949428716636027 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P089_replay :
    compactExp2620 momentScalarGrow2622K01P089Input 20 = momentScalarGrow2622K01P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P089] using h

theorem momentScalarGrow2622K01P089_radius_le :
    (momentScalarGrow2622K01P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P089Expected]

end ConnesWeilRH.Dev
