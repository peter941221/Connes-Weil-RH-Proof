import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P108 : ℚ := ((-803812943592061833225536063777190305319 : ℚ) / 26117658846622256004916875481002803200)

def momentPanelGrowth2622K13P108 : ℚ := ((4340095942279694619717784497665467024483 : ℚ) / 31407419782145991187919086734190156185600)

theorem momentPanelPhase_owner2622K13P108 :
    (momentPanelPhase2622K13P108 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (37 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P108 :
    (momentPanelGrowth2622K13P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P108Input : RatPair2542 := (momentPanelPhase2622K13P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P108Expected : RatState2542 :=
  ((((22984108951463542580059119422248865650204154396564497823016349390294180366798491019 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((116546698730240187651872681747708747 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K13P108_replay :
    compactExp2620 momentScalarAmp2622K13P108Input 20 = momentScalarAmp2622K13P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K13P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P108_replay] at h
  simpa only [momentPanelPhase_owner2622K13P108] using h

theorem momentScalarAmp2622K13P108_radius_le :
    (momentScalarAmp2622K13P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P108Expected]

def momentScalarGrow2622K13P108Input : RatPair2542 := (momentPanelGrowth2622K13P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P108Expected : RatState2542 :=
  ((((2452519379437837182586339776627718075011892571525405316055288242450398251341032767574050566570795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((777234313425826486471253860598201103925996889047 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K13P108_replay :
    compactExp2620 momentScalarGrow2622K13P108Input 20 = momentScalarGrow2622K13P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P108] using h

theorem momentScalarGrow2622K13P108_radius_le :
    (momentScalarGrow2622K13P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P108Expected]

end ConnesWeilRH.Dev
