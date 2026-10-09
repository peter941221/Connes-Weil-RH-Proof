import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P146 : ℚ := ((-72797725102452618299037920695930641326738242944389075 : ℚ) / 1658256295256575723566855903320712621177112461574144)

def momentPanelGrowth2622K03P146 : ℚ := ((3136283820998438212643224483830146186723578298215888425 : ℚ) / 4163087505280929295684628633722634226257612577162919936)

theorem momentPanelPhase_owner2622K03P146 :
    (momentPanelPhase2622K03P146 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P146 :
    (momentPanelGrowth2622K03P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P146Input : RatPair2542 := (momentPanelPhase2622K03P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P146Expected : RatState2542 :=
  ((((11478342569146908667151053859131459137201140416374516108870052822104167723941 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((232820610479601013625471305791 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P146_replay :
    compactExp2620 momentScalarAmp2622K03P146Input 20 = momentScalarAmp2622K03P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K03P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P146_replay] at h
  simpa only [momentPanelPhase_owner2622K03P146] using h

theorem momentScalarAmp2622K03P146_radius_le :
    (momentScalarAmp2622K03P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P146Expected]

def momentScalarGrow2622K03P146Input : RatPair2542 := (momentPanelGrowth2622K03P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P146Expected : RatState2542 :=
  ((((4537082117336795805718647541221294790260876134878705842478337322695240163164363128967052072113919 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5751430737177929367906491133958239051628195047943 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P146_replay :
    compactExp2620 momentScalarGrow2622K03P146Input 20 = momentScalarGrow2622K03P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P146] using h

theorem momentScalarGrow2622K03P146_radius_le :
    (momentScalarGrow2622K03P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P146Expected]

end ConnesWeilRH.Dev
