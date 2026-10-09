import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P106 : ℚ := ((-2415512582438526599821133656803947835393 : ℚ) / 78920884008769014786621149479016857600)

def momentPanelGrowth2622K05P106 : ℚ := ((3897877293546095011037123867564928158123 : ℚ) / 31878377333142782975163141909051447705600)

theorem momentPanelPhase_owner2622K05P106 :
    (momentPanelPhase2622K05P106 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P106 :
    (momentPanelGrowth2622K05P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P106Input : RatPair2542 := (momentPanelPhase2622K05P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P106Expected : RatState2542 :=
  ((((108956084842202840763987587570282981144182390503036604851658700224991108220267485639 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((17265284740885309791853716524811049 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P106_replay :
    compactExp2620 momentScalarAmp2622K05P106Input 20 = momentScalarAmp2622K05P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K05P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P106_replay] at h
  simpa only [momentPanelPhase_owner2622K05P106] using h

theorem momentScalarAmp2622K05P106_radius_le :
    (momentScalarAmp2622K05P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P106Expected]

def momentScalarGrow2622K05P106Input : RatPair2542 := (momentPanelGrowth2622K05P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P106Expected : RatState2542 :=
  ((((2413799935967463850379084123831407075467551068121134764529054694378635488617302870902234481465653 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((764963645213359157164040046782465032904286251697 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P106_replay :
    compactExp2620 momentScalarGrow2622K05P106Input 20 = momentScalarGrow2622K05P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P106] using h

theorem momentScalarGrow2622K05P106_radius_le :
    (momentScalarGrow2622K05P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P106Expected]

end ConnesWeilRH.Dev
