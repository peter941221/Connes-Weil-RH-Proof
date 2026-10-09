import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P006 : ℚ := ((-820944740640888424019808355573824240931 : ℚ) / 8188008756994179350147505344164659200)

def momentPanelGrowth2622K05P006 : ℚ := ((3127179559885600365453122674869636081 : ℚ) / 536469734016586682713404796515123200)

theorem momentPanelPhase_owner2622K05P006 :
    (momentPanelPhase2622K05P006 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-167 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P006, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P006 :
    (momentPanelGrowth2622K05P006 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P006, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P006Input : RatPair2542 := (momentPanelPhase2622K05P006 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P006Expected : RatState2542 :=
  ((((61156014048511237792821973069848387522028731430390783 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349490703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P006_replay :
    compactExp2620 momentScalarAmp2622K05P006Input 20 = momentScalarAmp2622K05P006Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P006_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-167 / 200) 0) -
      (momentScalarAmp2622K05P006Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P006]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P006 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P006 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P006Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P006_replay] at h
  simpa only [momentPanelPhase_owner2622K05P006] using h

theorem momentScalarAmp2622K05P006_radius_le :
    (momentScalarAmp2622K05P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P006Expected]

def momentScalarGrow2622K05P006Input : RatPair2542 := (momentPanelGrowth2622K05P006 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P006Expected : RatState2542 :=
  ((((726407068967926623346987747774183995318943113025038683357416804891565062765858628342046526069405291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((230206309493942242712281693647411735405785103378047 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P006_replay :
    compactExp2620 momentScalarGrow2622K05P006Input 20 = momentScalarGrow2622K05P006Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P006_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P006Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P006]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P006 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P006 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P006Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P006_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P006] using h

theorem momentScalarGrow2622K05P006_radius_le :
    (momentScalarGrow2622K05P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P006Expected]

end ConnesWeilRH.Dev
