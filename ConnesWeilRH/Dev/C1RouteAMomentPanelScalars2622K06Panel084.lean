import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P084 : ℚ := ((-20146223 : ℚ) / 664650)

def momentPanelGrowth2622K06P084 : ℚ := ((11830081 : ℚ) / 155127025)

theorem momentPanelPhase_owner2622K06P084 :
    (momentPanelPhase2622K06P084 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P084 :
    (momentPanelGrowth2622K06P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P084Input : RatPair2542 := (momentPanelPhase2622K06P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P084Expected : RatState2542 :=
  ((((36612347022391292807827912596336167299697854781771112177193623341204568987232672243 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((185652021254105654590398961681288485 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P084_replay :
    compactExp2620 momentScalarAmp2622K06P084Input 20 = momentScalarAmp2622K06P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K06P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P084_replay] at h
  simpa only [momentPanelPhase_owner2622K06P084] using h

theorem momentScalarAmp2622K06P084_radius_le :
    (momentScalarAmp2622K06P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P084Expected]

def momentScalarGrow2622K06P084Input : RatPair2542 := (momentPanelGrowth2622K06P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P084Expected : RatState2542 :=
  ((((2305250755536193864186895650683472132204560362735102522995686379696436564445100065787464702169051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((730563072850775266224079603733146911840330494699 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P084_replay :
    compactExp2620 momentScalarGrow2622K06P084Input 20 = momentScalarGrow2622K06P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P084] using h

theorem momentScalarGrow2622K06P084_radius_le :
    (momentScalarGrow2622K06P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P084Expected]

end ConnesWeilRH.Dev
