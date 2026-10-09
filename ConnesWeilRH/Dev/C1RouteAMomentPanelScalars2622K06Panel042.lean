import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P042 : ℚ := ((-167847 : ℚ) / 4130)

def momentPanelGrowth2622K06P042 : ℚ := ((3043861 : ℚ) / 5784025)

theorem momentPanelPhase_owner2622K06P042 :
    (momentPanelPhase2622K06P042 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P042 :
    (momentPanelGrowth2622K06P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P042Input : RatPair2542 := (momentPanelPhase2622K06P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P042Expected : RatState2542 :=
  ((((2390238730598418344171020733108981195221682046201616375533565530954804913726595 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6060212419205104588745403560225 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P042_replay :
    compactExp2620 momentScalarAmp2622K06P042Input 20 = momentScalarAmp2622K06P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K06P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P042_replay] at h
  simpa only [momentPanelPhase_owner2622K06P042] using h

theorem momentScalarAmp2622K06P042_radius_le :
    (momentScalarAmp2622K06P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P042Expected]

def momentScalarGrow2622K06P042Input : RatPair2542 := (momentPanelGrowth2622K06P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P042Expected : RatState2542 :=
  ((((1807662829010744479165614975545012669611216959328067275703395511352853154956404252096057162947107 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((572870930042305809351151467132532689098257863701 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P042_replay :
    compactExp2620 momentScalarGrow2622K06P042Input 20 = momentScalarGrow2622K06P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P042] using h

theorem momentScalarGrow2622K06P042_radius_le :
    (momentScalarGrow2622K06P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P042Expected]

end ConnesWeilRH.Dev
