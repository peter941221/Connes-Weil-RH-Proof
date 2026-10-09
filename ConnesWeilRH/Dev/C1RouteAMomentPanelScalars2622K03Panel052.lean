import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P052 : ℚ := ((-70375164394057984808641822648409485341600945013473 : ℚ) / 2009564751329991512530066644984889152026907246592)

def momentPanelGrowth2622K03P052 : ℚ := ((43800729517045623908603021148495072864180682134786475 : ℚ) / 139309148600301334804554197760589515453650019551281152)

theorem momentPanelPhase_owner2622K03P052 :
    (momentPanelPhase2622K03P052 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 8) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P052, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P052 :
    (momentPanelGrowth2622K03P052 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P052, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P052Input : RatPair2542 := (momentPanelPhase2622K03P052 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P052Expected : RatState2542 :=
  ((((1319961193858239575684626209738364309854511969582023514368632638469425859052289129 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1673305485833214614416641394632043 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P052_replay :
    compactExp2620 momentScalarAmp2622K03P052Input 20 = momentScalarAmp2622K03P052Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P052_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 8) 0) -
      (momentScalarAmp2622K03P052Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P052]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P052 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P052 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P052Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P052_replay] at h
  simpa only [momentPanelPhase_owner2622K03P052] using h

theorem momentScalarAmp2622K03P052_radius_le :
    (momentScalarAmp2622K03P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P052Expected]

def momentScalarGrow2622K03P052Input : RatPair2542 := (momentPanelGrowth2622K03P052 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P052Expected : RatState2542 :=
  ((((2925141129095343101406011349771077538887860363862752128956971698774999796277499609137107183215801 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3708055796195082604191785979275743046023056177733 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P052_replay :
    compactExp2620 momentScalarGrow2622K03P052Input 20 = momentScalarGrow2622K03P052Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P052_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P052Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P052]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P052 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P052 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P052Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P052_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P052] using h

theorem momentScalarGrow2622K03P052_radius_le :
    (momentScalarGrow2622K03P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P052Expected]

end ConnesWeilRH.Dev
