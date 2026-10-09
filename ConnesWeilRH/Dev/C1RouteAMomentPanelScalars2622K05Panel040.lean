import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P040 : ℚ := ((-2476675565335850264134872618037468924389 : ℚ) / 61250848762067679513278304158639718400)

def momentPanelGrowth2622K05P040 : ℚ := ((1665526572941143498040522808304547 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K05P040 :
    (momentPanelPhase2622K05P040 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P040 :
    (momentPanelGrowth2622K05P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P040Input : RatPair2542 := (momentPanelPhase2622K05P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P040Expected : RatState2542 :=
  ((((734224727393766269103901501639615108286810971322455134530179977700911605702561 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1861553220631236451168364949621 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P040_replay :
    compactExp2620 momentScalarAmp2622K05P040Input 20 = momentScalarAmp2622K05P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K05P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P040_replay] at h
  simpa only [momentPanelPhase_owner2622K05P040] using h

theorem momentScalarAmp2622K05P040_radius_le :
    (momentScalarAmp2622K05P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P040Expected]

def momentScalarGrow2622K05P040Input : RatPair2542 := (momentPanelGrowth2622K05P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P040Expected : RatState2542 :=
  ((((923190036136985215080364132811143511863280097092899566399535989114814453479051965004484466278331 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2340563584895125842457359727179696110458206974871 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P040_replay :
    compactExp2620 momentScalarGrow2622K05P040Input 20 = momentScalarGrow2622K05P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P040] using h

theorem momentScalarGrow2622K05P040_radius_le :
    (momentScalarGrow2622K05P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P040Expected]

end ConnesWeilRH.Dev
