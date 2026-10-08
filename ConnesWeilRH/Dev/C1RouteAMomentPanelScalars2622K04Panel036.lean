import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P036 : ℚ := ((-127943381560587947580666481745071580710492099517436113 : ℚ) / 2716623258296524037606341514250169042590919924121600)

def momentPanelGrowth2622K04P036 : ℚ := ((331409691271892024598896479518284765699918475499402407 : ℚ) / 447647818055837351530633150430614397505143820412518400)

theorem momentPanelPhase_owner2622K04P036 :
    (momentPanelPhase2622K04P036 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-107 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P036 :
    (momentPanelGrowth2622K04P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P036Input : RatPair2542 := (momentPanelPhase2622K04P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P036Expected : RatState2542 :=
  ((((1878447497906443813650356148627162210661498937019540073977472789345243157353 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((9527706060361420295897101207 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P036_replay :
    compactExp2620 momentScalarAmp2622K04P036Input 20 = momentScalarAmp2622K04P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K04P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P036_replay] at h
  simpa only [momentPanelPhase_owner2622K04P036] using h

theorem momentScalarAmp2622K04P036_radius_le :
    (momentScalarAmp2622K04P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P036Expected]

def momentScalarGrow2622K04P036Input : RatPair2542 := (momentPanelGrowth2622K04P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P036Expected : RatState2542 :=
  ((((4478394537224061267791223452421026231821351190535009360997432537017244406438576035656634777551955 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2838517757479916576810341170377961936435669202171 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P036_replay :
    compactExp2620 momentScalarGrow2622K04P036Input 20 = momentScalarGrow2622K04P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P036] using h

theorem momentScalarGrow2622K04P036_radius_le :
    (momentScalarGrow2622K04P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P036Expected]

end ConnesWeilRH.Dev
