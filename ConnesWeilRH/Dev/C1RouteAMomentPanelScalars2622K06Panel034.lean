import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P034 : ℚ := ((-63072369 : ℚ) / 1383950)

def momentPanelGrowth2622K06P034 : ℚ := ((1155097 : ℚ) / 1533675)

theorem momentPanelPhase_owner2622K06P034 :
    (momentPanelPhase2622K06P034 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-111 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P034, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P034 :
    (momentPanelGrowth2622K06P034 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P034, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P034Input : RatPair2542 := (momentPanelPhase2622K06P034 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P034Expected : RatState2542 :=
  ((((34434135564569838165423055235017351081568033560395315330680281025782848360059 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((21827383842729366776760680085 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P034_replay :
    compactExp2620 momentScalarAmp2622K06P034Input 20 = momentScalarAmp2622K06P034Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P034_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-111 / 200) 0) -
      (momentScalarAmp2622K06P034Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P034]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P034 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P034 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P034Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P034_replay] at h
  simpa only [momentPanelPhase_owner2622K06P034] using h

theorem momentScalarAmp2622K06P034_radius_le :
    (momentScalarAmp2622K06P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P034Expected]

def momentScalarGrow2622K06P034Input : RatPair2542 := (momentPanelGrowth2622K06P034 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P034Expected : RatState2542 :=
  ((((1134044899226739213795800688426066762975033041126335401617194878437443121121760428781472529674667 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1437571664631566865088297751779326878965495949181 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P034_replay :
    compactExp2620 momentScalarGrow2622K06P034Input 20 = momentScalarGrow2622K06P034Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P034_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P034Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P034]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P034 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P034 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P034Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P034_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P034] using h

theorem momentScalarGrow2622K06P034_radius_le :
    (momentScalarGrow2622K06P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P034Expected]

end ConnesWeilRH.Dev
