import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P022 : ℚ := ((-19840487636302648416473206783377742773 : ℚ) / 353319575295612098785161117402398720)

def momentPanelGrowth2622K25P022 : ℚ := ((212758691284083621814456990243709243 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K25P022 :
    (momentPanelPhase2622K25P022 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P022 :
    (momentPanelGrowth2622K25P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P022Input : RatPair2542 := (momentPanelPhase2622K25P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P022Expected : RatState2542 :=
  ((((874993386593485704442887928969899209399723652542727528146462047175008693 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3527096932892355156283389 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K25P022_replay :
    compactExp2620 momentScalarAmp2622K25P022Input 20 = momentScalarAmp2622K25P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K25P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P022_replay] at h
  simpa only [momentPanelPhase_owner2622K25P022] using h

theorem momentScalarAmp2622K25P022_radius_le :
    (momentScalarAmp2622K25P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P022Expected]

def momentScalarGrow2622K25P022Input : RatPair2542 := (momentPanelGrowth2622K25P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P022Expected : RatState2542 :=
  ((((2225140327415508536393544672627651493900455633077028150108294093771090285148032536761056246280139 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2820696632471712667818850741536272652426046634289 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K25P022_replay :
    compactExp2620 momentScalarGrow2622K25P022Input 20 = momentScalarGrow2622K25P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P022] using h

theorem momentScalarGrow2622K25P022_radius_le :
    (momentScalarGrow2622K25P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P022Expected]

end ConnesWeilRH.Dev
