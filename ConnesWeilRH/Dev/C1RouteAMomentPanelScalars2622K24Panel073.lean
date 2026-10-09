import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P073 : ℚ := ((-2454057542188409395432936011656266814247 : ℚ) / 78920884008769014786621149479016857600)

def momentPanelGrowth2622K24P073 : ℚ := ((3941741940756499524353790268086824388083 : ℚ) / 31878377333142782975163141909051447705600)

theorem momentPanelPhase_owner2622K24P073 :
    (momentPanelPhase2622K24P073 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P073 :
    (momentPanelGrowth2622K24P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P073Input : RatPair2542 := (momentPanelPhase2622K24P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P073Expected : RatState2542 :=
  ((((8357032232940486502687793728147833804986559229203263253537245681937960774429444981 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((84752888692602070418060932939102043 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K24P073_replay :
    compactExp2620 momentScalarAmp2622K24P073Input 20 = momentScalarAmp2622K24P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K24P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P073_replay] at h
  simpa only [momentPanelPhase_owner2622K24P073] using h

theorem momentScalarAmp2622K24P073_radius_le :
    (momentScalarAmp2622K24P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P073Expected]

def momentScalarGrow2622K24P073Input : RatPair2542 := (momentPanelGrowth2622K24P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P073Expected : RatState2542 :=
  ((((2417123610843255791902161942943544884818926927097168093638091656430337585215094758383597654888305 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((95752119837267281323227333770316909153652816191 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K24P073_replay :
    compactExp2620 momentScalarGrow2622K24P073Input 20 = momentScalarGrow2622K24P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P073] using h

theorem momentScalarGrow2622K24P073_radius_le :
    (momentScalarGrow2622K24P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P073Expected]

end ConnesWeilRH.Dev
