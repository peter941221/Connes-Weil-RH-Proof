import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P010 : ℚ := ((-105020213895605958681517795213215750075 : ℚ) / 1194147147824595747880318366715478016)

def momentPanelGrowth2622K07P010 : ℚ := ((4144908034305396820823274977867225 : ℚ) / 1095250118597190202893151569444864)

theorem momentPanelPhase_owner2622K07P010 :
    (momentPanelPhase2622K07P010 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P010 :
    (momentPanelGrowth2622K07P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P010Input : RatPair2542 := (momentPanelPhase2622K07P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P010Expected : RatState2542 :=
  ((((3413244991057329653900295010176579580165173619197921464915 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229275658458855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P010_replay :
    compactExp2620 momentScalarAmp2622K07P010Input 20 = momentScalarAmp2622K07P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K07P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P010_replay] at h
  simpa only [momentPanelPhase_owner2622K07P010] using h

theorem momentScalarAmp2622K07P010_radius_le :
    (momentScalarAmp2622K07P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P010Expected]

def momentScalarGrow2622K07P010Input : RatPair2542 := (momentPanelGrowth2622K07P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P010Expected : RatState2542 :=
  ((((94006934935457438262112123954192869806170253809458863764168516273904008152054814360818927099702333 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((59583758702775476073795844908242686249815014107063 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P010_replay :
    compactExp2620 momentScalarGrow2622K07P010Input 20 = momentScalarGrow2622K07P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P010] using h

theorem momentScalarGrow2622K07P010_radius_le :
    (momentScalarGrow2622K07P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P010Expected]

end ConnesWeilRH.Dev
