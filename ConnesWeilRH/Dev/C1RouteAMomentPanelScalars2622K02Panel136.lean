import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P136 : ℚ := ((-325526004651451322408820784925841704316389473319867403 : ℚ) / 8949128482804909646211664685642224404147097881804800)

def momentPanelGrowth2622K02P136 : ℚ := ((1459678323353434850197412011882212928232655907631940133 : ℚ) / 2887782655174593052634530025078670012982807132687564800)

theorem momentPanelPhase_owner2622K02P136 :
    (momentPanelPhase2622K02P136 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (93 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P136, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P136 :
    (momentPanelGrowth2622K02P136 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P136, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P136Input : RatPair2542 := (momentPanelPhase2622K02P136 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P136Expected : RatState2542 :=
  ((((340460059192743847755190448641270464080024404487804918284120394114906971692763927 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((431599372754956563228873045758857 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P136_replay :
    compactExp2620 momentScalarAmp2622K02P136Input 20 = momentScalarAmp2622K02P136Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P136_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (93 / 200) 0) -
      (momentScalarAmp2622K02P136Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P136]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P136 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P136 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P136Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P136_replay] at h
  simpa only [momentPanelPhase_owner2622K02P136] using h

theorem momentScalarAmp2622K02P136_radius_le :
    (momentScalarAmp2622K02P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P136Expected]

def momentScalarGrow2622K02P136Input : RatPair2542 := (momentPanelGrowth2622K02P136 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P136Expected : RatState2542 :=
  ((((3540952201504963898769179384687354330066360230714869613393036785425069552053200502196473481106535 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4488688019841394893537604566060283616314694808733 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P136_replay :
    compactExp2620 momentScalarGrow2622K02P136Input 20 = momentScalarGrow2622K02P136Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P136_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P136Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P136Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P136 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P136]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P136 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P136 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P136Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P136Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P136_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P136] using h

theorem momentScalarGrow2622K02P136_radius_le :
    (momentScalarGrow2622K02P136Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P136Expected]

end ConnesWeilRH.Dev
