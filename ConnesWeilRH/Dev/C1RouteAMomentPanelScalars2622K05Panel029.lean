import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P029 : ℚ := ((-825934135324222725676230205028002663357 : ℚ) / 17144720837966757009362611512069324800)

def momentPanelGrowth2622K05P029 : ℚ := ((12560347786629399370876013292239489160283 : ℚ) / 13327517602174062958649115359825205657600)

theorem momentPanelPhase_owner2622K05P029 :
    (momentPanelPhase2622K05P029 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-121 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P029, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P029 :
    (momentPanelGrowth2622K05P029 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P029, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P029Input : RatPair2542 := (momentPanelPhase2622K05P029 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P029Expected : RatState2542 :=
  ((((639331299546194172698904902825609336160237560664719356250208757487439228337 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((811090403458723199078855705 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P029_replay :
    compactExp2620 momentScalarAmp2622K05P029Input 20 = momentScalarAmp2622K05P029Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P029_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-121 / 200) 0) -
      (momentScalarAmp2622K05P029Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P029]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P029 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P029 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P029Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P029_replay] at h
  simpa only [momentPanelPhase_owner2622K05P029] using h

theorem momentScalarAmp2622K05P029_radius_le :
    (momentScalarAmp2622K05P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P029Expected]

def momentScalarGrow2622K05P029Input : RatPair2542 := (momentPanelGrowth2622K05P029 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P029Expected : RatState2542 :=
  ((((5481429956217623096248518961971402002857109245894702602396775031811652194421027960487604315705327 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3474265864458621048622816687208107252072939778165 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P029_replay :
    compactExp2620 momentScalarGrow2622K05P029Input 20 = momentScalarGrow2622K05P029Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P029_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P029Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P029]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P029 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P029 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P029Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P029_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P029] using h

theorem momentScalarGrow2622K05P029_radius_le :
    (momentScalarGrow2622K05P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P029Expected]

end ConnesWeilRH.Dev
