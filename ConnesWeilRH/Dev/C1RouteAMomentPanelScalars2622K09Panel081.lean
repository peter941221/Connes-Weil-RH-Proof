import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P081 : ℚ := ((-814830846689648999907813097747628620701 : ℚ) / 26847825592353716140178976527299379200)

def momentPanelGrowth2622K09P081 : ℚ := ((7021578593583045617009268864863649406009 : ℚ) / 99775826484833044745879104971697081548800)

theorem momentPanelPhase_owner2622K09P081 :
    (momentPanelPhase2622K09P081 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P081 :
    (momentPanelGrowth2622K09P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P081Input : RatPair2542 := (momentPanelPhase2622K09P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P081Expected : RatState2542 :=
  ((((8803427276022799703243774477887351959708421258412177188618487150130964532636138827 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((178559886091802526531325913867249623 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K09P081_replay :
    compactExp2620 momentScalarAmp2622K09P081Input 20 = momentScalarAmp2622K09P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K09P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P081_replay] at h
  simpa only [momentPanelPhase_owner2622K09P081] using h

theorem momentScalarAmp2622K09P081_radius_le :
    (momentScalarAmp2622K09P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P081Expected]

def momentScalarGrow2622K09P081Input : RatPair2542 := (momentPanelGrowth2622K09P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P081Expected : RatState2542 :=
  ((((2291719471066601164409466577173090571530182754140006491619583107757862038718114155020045309652569 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1452549684040536155056950212875974142377979162281 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K09P081_replay :
    compactExp2620 momentScalarGrow2622K09P081Input 20 = momentScalarGrow2622K09P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P081] using h

theorem momentScalarGrow2622K09P081_radius_le :
    (momentScalarGrow2622K09P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P081Expected]

end ConnesWeilRH.Dev
