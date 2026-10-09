import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P138 : ℚ := ((-72807619836601920844659954968912940637487173085636675 : ℚ) / 1862866524482902132115371779900992243928943017590784)

def momentPanelGrowth2622K03P138 : ℚ := ((900374619633864997989847601969040998402709090396409475 : ℚ) / 1758210858517649170041480377748334425618977357574438912)

theorem momentPanelPhase_owner2622K03P138 :
    (momentPanelPhase2622K03P138 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P138 :
    (momentPanelGrowth2622K03P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P138Input : RatPair2542 := (momentPanelPhase2622K03P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P138Expected : RatState2542 :=
  ((((22687460078628132250621055932907011406410254789711255481993713767551649970469229 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14380423394603863784616026795427 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P138_replay :
    compactExp2620 momentScalarAmp2622K03P138Input 20 = momentScalarAmp2622K03P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K03P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P138_replay] at h
  simpa only [momentPanelPhase_owner2622K03P138] using h

theorem momentScalarAmp2622K03P138_radius_le :
    (momentScalarAmp2622K03P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P138Expected]

def momentScalarGrow2622K03P138Input : RatPair2542 := (momentPanelGrowth2622K03P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P138Expected : RatState2542 :=
  ((((1782253786930290678483921384992366392880484217660729432915944195959604873946297895457200192338935 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4518547958781378316497529743115906765341110555611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P138_replay :
    compactExp2620 momentScalarGrow2622K03P138Input 20 = momentScalarGrow2622K03P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P138] using h

theorem momentScalarGrow2622K03P138_radius_le :
    (momentScalarGrow2622K03P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P138Expected]

end ConnesWeilRH.Dev
