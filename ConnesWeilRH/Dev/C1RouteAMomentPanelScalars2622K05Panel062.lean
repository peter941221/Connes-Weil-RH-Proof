import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P062 : ℚ := ((-6567981080705728033379280308695245647 : ℚ) / 199984558692005470380119897680117760)

def momentPanelGrowth2622K05P062 : ℚ := ((5802391913714627479806352828809403 : ℚ) / 27381252964929755072328789236121600)

theorem momentPanelPhase_owner2622K05P062 :
    (momentPanelPhase2622K05P062 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P062 :
    (momentPanelGrowth2622K05P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P062Input : RatPair2542 := (momentPanelPhase2622K05P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P062Expected : RatState2542 :=
  ((((11649510848745373149130251195474777089074399898287295499051972049311672012598602705 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14767971962490873104842521142524605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P062_replay :
    compactExp2620 momentScalarAmp2622K05P062Input 20 = momentScalarAmp2622K05P062Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622K05P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P062]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P062 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P062_replay] at h
  simpa only [momentPanelPhase_owner2622K05P062] using h

theorem momentScalarAmp2622K05P062_radius_le :
    (momentScalarAmp2622K05P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P062Expected]

def momentScalarGrow2622K05P062Input : RatPair2542 := (momentPanelGrowth2622K05P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P062Expected : RatState2542 :=
  ((((2640161182392244176102278186524465192161153428051714602736360233618803283211928098245944959605017 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3346801231189647650893348465788493630925093783083 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P062_replay :
    compactExp2620 momentScalarGrow2622K05P062Input 20 = momentScalarGrow2622K05P062Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P062_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P062] using h

theorem momentScalarGrow2622K05P062_radius_le :
    (momentScalarGrow2622K05P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P062Expected]

end ConnesWeilRH.Dev
