import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P117 : ℚ := ((-6412761065631341037946960514354994353 : ℚ) / 199984558692005470380119897680117760)

def momentPanelGrowth2622K05P117 : ℚ := ((5802391913714627479806352828809403 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K05P117 :
    (momentPanelPhase2622K05P117 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (11 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P117, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P117 :
    (momentPanelGrowth2622K05P117 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P117, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P117Input : RatPair2542 := (momentPanelPhase2622K05P117 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P117Expected : RatState2542 :=
  ((((3164460712928925130292473381191945987156427223369839928090951783614560354314356469 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((32092425576240062777780759320708133 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P117_replay :
    compactExp2620 momentScalarAmp2622K05P117Input 20 = momentScalarAmp2622K05P117Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P117_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (11 / 40) 0) -
      (momentScalarAmp2622K05P117Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P117]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P117 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P117 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P117Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P117_replay] at h
  simpa only [momentPanelPhase_owner2622K05P117] using h

theorem momentScalarAmp2622K05P117_radius_le :
    (momentScalarAmp2622K05P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P117Expected]

def momentScalarGrow2622K05P117Input : RatPair2542 := (momentPanelGrowth2622K05P117 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P117Expected : RatState2542 :=
  ((((2640161182392244176102278186524465192161153428051714602736360233618803283211928098245944959605017 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3346801231189647650893348465788493630925093783083 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P117_replay :
    compactExp2620 momentScalarGrow2622K05P117Input 20 = momentScalarGrow2622K05P117Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P117_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P117Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P117]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P117 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P117 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P117Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P117_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P117] using h

theorem momentScalarGrow2622K05P117_radius_le :
    (momentScalarGrow2622K05P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P117Expected]

end ConnesWeilRH.Dev
