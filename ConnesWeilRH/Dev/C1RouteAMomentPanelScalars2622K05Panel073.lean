import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P073 : ℚ := ((-2452265722437874301926206651839892164607 : ℚ) / 78920884008769014786621149479016857600)

def momentPanelGrowth2622K05P073 : ℚ := ((3897877293546095011037123867564928158123 : ℚ) / 31878377333142782975163141909051447705600)

theorem momentPanelPhase_owner2622K05P073 :
    (momentPanelPhase2622K05P073 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P073 :
    (momentPanelGrowth2622K05P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P073Input : RatPair2542 := (momentPanelPhase2622K05P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P073Expected : RatState2542 :=
  ((((1068617574115139869301416149719366482833133793608888833507445963513593253741599951 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((86699126511331947470396526528082355 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P073_replay :
    compactExp2620 momentScalarAmp2622K05P073Input 20 = momentScalarAmp2622K05P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K05P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P073_replay] at h
  simpa only [momentPanelPhase_owner2622K05P073] using h

theorem momentScalarAmp2622K05P073_radius_le :
    (momentScalarAmp2622K05P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P073Expected]

def momentScalarGrow2622K05P073Input : RatPair2542 := (momentPanelGrowth2622K05P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P073Expected : RatState2542 :=
  ((((2413799935967463850379084123831407075467551068121134764529054694378635488617302870902234481465653 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((764963645213359157164040046782465032904286251697 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P073_replay :
    compactExp2620 momentScalarGrow2622K05P073Input 20 = momentScalarGrow2622K05P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P073] using h

theorem momentScalarGrow2622K05P073_radius_le :
    (momentScalarGrow2622K05P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P073Expected]

end ConnesWeilRH.Dev
