import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P117 : ℚ := ((-154577 : ℚ) / 4930)

def momentPanelGrowth2622K06P117 : ℚ := ((657467 : ℚ) / 2764800)

theorem momentPanelPhase_owner2622K06P117 :
    (momentPanelPhase2622K06P117 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (11 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P117, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P117 :
    (momentPanelGrowth2622K06P117 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P117, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P117Input : RatPair2542 := (momentPanelPhase2622K06P117 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P117Expected : RatState2542 :=
  ((((25795421407109820852617585433869910851207325317030472674322085250426381115190883985 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((65401118447263715778786063247764587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P117_replay :
    compactExp2620 momentScalarAmp2622K06P117Input 20 = momentScalarAmp2622K06P117Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P117_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (11 / 40) 0) -
      (momentScalarAmp2622K06P117Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P117]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P117 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P117 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P117Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P117_replay] at h
  simpa only [momentPanelPhase_owner2622K06P117] using h

theorem momentScalarAmp2622K06P117_radius_le :
    (momentScalarAmp2622K06P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P117Expected]

def momentScalarGrow2622K06P117Input : RatPair2542 := (momentPanelGrowth2622K06P117 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P117Expected : RatState2542 :=
  ((((2709402062034268274806725378367292756556666733397607832652128389616546258395751428877002287499217 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((429321796411810133288037839386411686684729110275 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P117_replay :
    compactExp2620 momentScalarGrow2622K06P117Input 20 = momentScalarGrow2622K06P117Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P117_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P117Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P117Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P117 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P117]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P117 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P117 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P117Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P117Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P117_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P117] using h

theorem momentScalarGrow2622K06P117_radius_le :
    (momentScalarGrow2622K06P117Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P117Expected]

end ConnesWeilRH.Dev
