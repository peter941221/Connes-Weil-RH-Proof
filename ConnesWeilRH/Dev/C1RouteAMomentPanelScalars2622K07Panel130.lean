import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P130 : ℚ := ((-88484923662018449544241611670023804075 : ℚ) / 2712893978946032829225488543012356096)

def momentPanelGrowth2622K07P130 : ℚ := ((408182091354636126680672717808764566025 : ℚ) / 935773061022948153740308099404643958784)

theorem momentPanelPhase_owner2622K07P130 :
    (momentPanelPhase2622K07P130 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (81 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P130, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P130 :
    (momentPanelGrowth2622K07P130 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P130, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P130Input : RatPair2542 := (momentPanelPhase2622K07P130 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P130Expected : RatState2542 :=
  ((((14603666530639617471173410869629088165181742622400716429038933258326630684329282177 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18512922489420381903697889675087991 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P130_replay :
    compactExp2620 momentScalarAmp2622K07P130Input 20 = momentScalarAmp2622K07P130Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P130_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (81 / 200) 0) -
      (momentScalarAmp2622K07P130Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P130]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P130 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P130 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P130Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P130_replay] at h
  simpa only [momentPanelPhase_owner2622K07P130] using h

theorem momentScalarAmp2622K07P130_radius_le :
    (momentScalarAmp2622K07P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P130Expected]

def momentScalarGrow2622K07P130Input : RatPair2542 := (momentPanelGrowth2622K07P130 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P130Expected : RatState2542 :=
  ((((825993997373992766906656512116793172690169768997896713265378568225755409343933147609708113049979 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1047071350984148931676398379641098292419054126097 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P130_replay :
    compactExp2620 momentScalarGrow2622K07P130Input 20 = momentScalarGrow2622K07P130Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P130_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P130Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P130]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P130 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P130 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P130Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P130_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P130] using h

theorem momentScalarGrow2622K07P130_radius_le :
    (momentScalarGrow2622K07P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P130Expected]

end ConnesWeilRH.Dev
