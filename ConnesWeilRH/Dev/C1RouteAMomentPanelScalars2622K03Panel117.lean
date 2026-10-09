import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P117 : ℚ := ((-2915671187963665846121474953148049046227113206308125 : ℚ) / 90065038400516892334302077816140941086296842960896)

def momentPanelGrowth2622K03P117 : ℚ := ((495129791107209390725764950313277830063487587475 : ℚ) / 2466284012995898674468718155208727595669386166272)

theorem momentPanelPhase_owner2622K03P117 :
    (momentPanelPhase2622K03P117 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (11 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P117, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P117 :
    (momentPanelGrowth2622K03P117 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P117, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P117Input : RatPair2542 := (momentPanelPhase2622K03P117 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P117Expected : RatState2542 :=
  ((((9314811906754805955590990506762773292331255617208808032917980625294958478018209979 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((23616582921126460066312265373735301 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P117_replay :
    compactExp2620 momentScalarAmp2622K03P117Input 20 = momentScalarAmp2622K03P117Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P117_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (11 / 40) 0) -
      (momentScalarAmp2622K03P117Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P117]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P117 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P117 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P117Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P117_replay] at h
  simpa only [momentPanelPhase_owner2622K03P117] using h

theorem momentScalarAmp2622K03P117_radius_le :
    (momentScalarAmp2622K03P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P117Expected]

def momentScalarGrow2622K03P117Input : RatPair2542 := (momentPanelGrowth2622K03P117 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P117Expected : RatState2542 :=
  ((((652720626593659875478054032275458102812324325752469199948561311315455626012172006509375575467437 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3309686142661541116011452639752752753705790770443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P117_replay :
    compactExp2620 momentScalarGrow2622K03P117Input 20 = momentScalarGrow2622K03P117Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P117_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P117Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P117]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P117 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P117 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P117Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P117_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P117] using h

theorem momentScalarGrow2622K03P117_radius_le :
    (momentScalarGrow2622K03P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P117Expected]

end ConnesWeilRH.Dev
