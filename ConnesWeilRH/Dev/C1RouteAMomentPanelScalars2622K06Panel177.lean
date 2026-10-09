import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P177 : ℚ := ((-249 : ℚ) / 2)

def momentPanelGrowth2622K06P177 : ℚ := ((1725377 : ℚ) / 165675)

theorem momentPanelPhase_owner2622K06P177 :
    (momentPanelPhase2622K06P177 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P177 :
    (momentPanelGrowth2622K06P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P177Input : RatPair2542 := (momentPanelPhase2622K06P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P177Expected : RatState2542 :=
  ((((1819431106596393996395798817784992834628159 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P177_replay :
    compactExp2620 momentScalarAmp2622K06P177Input 20 = momentScalarAmp2622K06P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K06P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P177_replay] at h
  simpa only [momentPanelPhase_owner2622K06P177] using h

theorem momentScalarAmp2622K06P177_radius_le :
    (momentScalarAmp2622K06P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P177Expected]

def momentScalarGrow2622K06P177Input : RatPair2542 := (momentPanelGrowth2622K06P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P177Expected : RatState2542 :=
  ((((17798351848159105763955862371735212902022437071341044668490632632975681698102424243787967161548596613 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((90247469291063524755187707845385364780048983031831671 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P177_replay :
    compactExp2620 momentScalarGrow2622K06P177Input 20 = momentScalarGrow2622K06P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P177] using h

theorem momentScalarGrow2622K06P177_radius_le :
    (momentScalarGrow2622K06P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P177Expected]

end ConnesWeilRH.Dev
