import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P010 : ℚ := ((-2470647867601396296669309177097730743449 : ℚ) / 29853678695614893697007959167886950400)

def momentPanelGrowth2622K09P010 : ℚ := ((101836128864179184277582232949944963 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K09P010 :
    (momentPanelPhase2622K09P010 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P010 :
    (momentPanelGrowth2622K09P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P010Input : RatPair2542 := (momentPanelPhase2622K09P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P010Expected : RatState2542 :=
  ((((1221734231575396900317016973223960279485240100022171564380835 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639232356063324533 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K09P010_replay :
    compactExp2620 momentScalarAmp2622K09P010Input 20 = momentScalarAmp2622K09P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K09P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P010_replay] at h
  simpa only [momentPanelPhase_owner2622K09P010] using h

theorem momentScalarAmp2622K09P010_radius_le :
    (momentScalarAmp2622K09P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P010Expected]

def momentScalarGrow2622K09P010Input : RatPair2542 := (momentPanelGrowth2622K09P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P010Expected : RatState2542 :=
  ((((88068996240264453910036232505274955116482189408231105147680626393288713212291323712021422935790883 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((111640319967983085811715489460670277503500824288355 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P010_replay :
    compactExp2620 momentScalarGrow2622K09P010Input 20 = momentScalarGrow2622K09P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P010] using h

theorem momentScalarGrow2622K09P010_radius_le :
    (momentScalarGrow2622K09P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P010Expected]

end ConnesWeilRH.Dev
