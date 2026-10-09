import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P156 : ℚ := ((-28479235433719463694921673340723329758525468783733967 : ℚ) / 530722054532711181771523637739794766463924332134400)

def momentPanelGrowth2622K01P156 : ℚ := ((478800608648212567748393822673959767338464867183184011 : ℚ) / 361225936434529374739723426922941001466599166915379200)

theorem momentPanelPhase_owner2622K01P156 :
    (momentPanelPhase2622K01P156 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P156 :
    (momentPanelGrowth2622K01P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P156Input : RatPair2542 := (momentPanelPhase2622K01P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P156Expected : RatState2542 :=
  ((((5293733756888628318311207297853960424607517122168765849332967442776239317 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15839748041368060331529979 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P156_replay :
    compactExp2620 momentScalarAmp2622K01P156Input 20 = momentScalarAmp2622K01P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K01P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P156_replay] at h
  simpa only [momentPanelPhase_owner2622K01P156] using h

theorem momentScalarAmp2622K01P156_radius_le :
    (momentScalarAmp2622K01P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P156Expected]

def momentScalarGrow2622K01P156Input : RatPair2542 := (momentPanelGrowth2622K01P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P156Expected : RatState2542 :=
  ((((2009975218071814097477901811611172645797948829916699267280493580633112814694685346046175794133455 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((10191772283268343670344744308774588070797206020765 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P156_replay :
    compactExp2620 momentScalarGrow2622K01P156Input 20 = momentScalarGrow2622K01P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P156] using h

theorem momentScalarGrow2622K01P156_radius_le :
    (momentScalarGrow2622K01P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P156Expected]

end ConnesWeilRH.Dev
