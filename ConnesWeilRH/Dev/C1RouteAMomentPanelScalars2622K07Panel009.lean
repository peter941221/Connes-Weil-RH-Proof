import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P009 : ℚ := ((-34926388103333445887696529674895205975 : ℚ) / 380741393079749157198337801141092352)

def momentPanelGrowth2622K07P009 : ℚ := ((2010183212525556422117624363304324030075 : ℚ) / 479748799180217774575951719353204867072)

theorem momentPanelPhase_owner2622K07P009 :
    (momentPanelPhase2622K07P009 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-161 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P009 :
    (momentPanelGrowth2622K07P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P009Input : RatPair2542 := (momentPanelPhase2622K07P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P009Expected : RatState2542 :=
  ((((309490849713056739625042059609517297399550944515935302781 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258741831145 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P009_replay :
    compactExp2620 momentScalarAmp2622K07P009Input 20 = momentScalarAmp2622K07P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K07P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P009_replay] at h
  simpa only [momentPanelPhase_owner2622K07P009] using h

theorem momentScalarAmp2622K07P009_radius_le :
    (momentScalarAmp2622K07P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P009Expected]

def momentScalarGrow2622K07P009Input : RatPair2542 := (momentPanelGrowth2622K07P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P009Expected : RatState2542 :=
  ((((141034333019481233861618784889210202842151388754054388616641022018754631857007754528910410391527165 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((89390771249231066265351932893794260194302039787249 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P009_replay :
    compactExp2620 momentScalarGrow2622K07P009Input 20 = momentScalarGrow2622K07P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P009] using h

theorem momentScalarGrow2622K07P009_radius_le :
    (momentScalarGrow2622K07P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P009Expected]

end ConnesWeilRH.Dev
