import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P049 : ℚ := ((-106226208533037586525652000675729795925 : ℚ) / 2712893978946032829225488543012356096)

def momentPanelGrowth2622K07P049 : ℚ := ((408182091354636126680672717808764566025 : ℚ) / 935773061022948153740308099404643958784)

theorem momentPanelPhase_owner2622K07P049 :
    (momentPanelPhase2622K07P049 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P049 :
    (momentPanelGrowth2622K07P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P049Input : RatPair2542 := (momentPanelPhase2622K07P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P049Expected : RatState2542 :=
  ((((21102930316604047090554465497301864128747541198450902257016176367182474564628061 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3344017957903734583623757245793 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P049_replay :
    compactExp2620 momentScalarAmp2622K07P049Input 20 = momentScalarAmp2622K07P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K07P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P049_replay] at h
  simpa only [momentPanelPhase_owner2622K07P049] using h

theorem momentScalarAmp2622K07P049_radius_le :
    (momentScalarAmp2622K07P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P049Expected]

def momentScalarGrow2622K07P049Input : RatPair2542 := (momentPanelGrowth2622K07P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P049Expected : RatState2542 :=
  ((((825993997373992766906656512116793172690169768997896713265378568225755409343933147609708113049979 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1047071350984148931676398379641098292419054126097 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P049_replay :
    compactExp2620 momentScalarGrow2622K07P049Input 20 = momentScalarGrow2622K07P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P049] using h

theorem momentScalarGrow2622K07P049_radius_le :
    (momentScalarGrow2622K07P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P049Expected]

end ConnesWeilRH.Dev
