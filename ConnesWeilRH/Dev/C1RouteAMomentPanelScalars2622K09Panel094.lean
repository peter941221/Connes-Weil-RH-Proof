import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P094 : ℚ := ((-2428246191342095884570652308756423514001 : ℚ) / 80965350896817103165355032408647270400)

def momentPanelGrowth2622K09P094 : ℚ := ((2456100110902533638375499953980316723 : ℚ) / 53816331521849159719380439199750553600)

theorem momentPanelPhase_owner2622K09P094 :
    (momentPanelPhase2622K09P094 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P094 :
    (momentPanelGrowth2622K09P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P094Input : RatPair2542 := (momentPanelPhase2622K09P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P094Expected : RatState2542 :=
  ((((100824441126252468305487155879824591209838672175793191289272473819818373723860532875 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((255627637935130073302747822110803765 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K09P094_replay :
    compactExp2620 momentScalarAmp2622K09P094Input 20 = momentScalarAmp2622K09P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K09P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P094_replay] at h
  simpa only [momentPanelPhase_owner2622K09P094] using h

theorem momentScalarAmp2622K09P094_radius_le :
    (momentScalarAmp2622K09P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P094Expected]

def momentScalarGrow2622K09P094Input : RatPair2542 := (momentPanelGrowth2622K09P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P094Expected : RatState2542 :=
  ((((2235729149248666923338451688837203784173361463610364105425469504958981951612910103104368110360957 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2834123274639511390239346228537533057027824350489 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P094_replay :
    compactExp2620 momentScalarGrow2622K09P094Input 20 = momentScalarGrow2622K09P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P094] using h

theorem momentScalarGrow2622K09P094_radius_le :
    (momentScalarGrow2622K09P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P094Expected]

end ConnesWeilRH.Dev
