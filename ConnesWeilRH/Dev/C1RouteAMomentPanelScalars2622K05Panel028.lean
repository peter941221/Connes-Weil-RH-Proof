import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P028 : ℚ := ((-2477669225310646948430175663211785015837 : ℚ) / 50444380925242069511399208673450393600)

def momentPanelGrowth2622K05P028 : ℚ := ((797242218577177505859800400376655753123 : ℚ) / 800655217947510968069966126053431705600)

theorem momentPanelPhase_owner2622K05P028 :
    (momentPanelPhase2622K05P028 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-123 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P028 :
    (momentPanelGrowth2622K05P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P028Input : RatPair2542 := (momentPanelPhase2622K05P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P028Expected : RatState2542 :=
  ((((498184876167797697616193865682293618124789850236203057495624478844607319413 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1265525730694686318500815611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P028_replay :
    compactExp2620 momentScalarAmp2622K05P028Input 20 = momentScalarAmp2622K05P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K05P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P028_replay] at h
  simpa only [momentPanelPhase_owner2622K05P028] using h

theorem momentScalarAmp2622K05P028_radius_le :
    (momentScalarAmp2622K05P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P028Expected]

def momentScalarGrow2622K05P028Input : RatPair2542 := (momentPanelGrowth2622K05P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P028Expected : RatState2542 :=
  ((((1445379233869018751087435337850486384861745253152169058512694503628642296908229951045314360295803 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((458058528366146991835657226248773975917553341427 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K05P028_replay :
    compactExp2620 momentScalarGrow2622K05P028Input 20 = momentScalarGrow2622K05P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P028] using h

theorem momentScalarGrow2622K05P028_radius_le :
    (momentScalarGrow2622K05P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P028Expected]

end ConnesWeilRH.Dev
