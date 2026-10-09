import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P135 : ℚ := ((-29300797358677799121434408790446081275 : ℚ) / 857783666957636445569577151388188672)

def momentPanelGrowth2622K07P135 : ℚ := ((27565775877373004870457606406685703025 : ℚ) / 52529290938039839320958442422145122304)

theorem momentPanelPhase_owner2622K07P135 :
    (momentPanelPhase2622K07P135 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (91 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P135, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P135 :
    (momentPanelGrowth2622K07P135 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P135, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P135Input : RatPair2542 := (momentPanelPhase2622K07P135 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P135Expected : RatState2542 :=
  ((((3123577927241168466812552959714909482354721378920432415577744261890060387568766825 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3959734428139472826466850601428989 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P135_replay :
    compactExp2620 momentScalarAmp2622K07P135Input 20 = momentScalarAmp2622K07P135Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P135_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (91 / 200) 0) -
      (momentScalarAmp2622K07P135Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P135]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P135 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P135 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P135Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P135_replay] at h
  simpa only [momentPanelPhase_owner2622K07P135] using h

theorem momentScalarAmp2622K07P135_radius_le :
    (momentScalarAmp2622K07P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P135Expected]

def momentScalarGrow2622K07P135Input : RatPair2542 := (momentPanelGrowth2622K07P135 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P135Expected : RatState2542 :=
  ((((3609966413543518092892533565580256890088286225958580236964164509073702086067444586958771775546901 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2288086900371426868776245376702699459628609266891 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P135_replay :
    compactExp2620 momentScalarGrow2622K07P135Input 20 = momentScalarGrow2622K07P135Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P135_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P135Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P135]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P135 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P135 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P135Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P135_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P135] using h

theorem momentScalarGrow2622K07P135_radius_le :
    (momentScalarGrow2622K07P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P135Expected]

end ConnesWeilRH.Dev
