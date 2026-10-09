import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P157 : ℚ := ((-19134555124862015282115503166762369987 : ℚ) / 353319575295612098785161117402398720)

def momentPanelGrowth2622K05P157 : ℚ := ((212553563106316130074963510645740083 : ℚ) / 149075710586839777616012296952217600)

theorem momentPanelPhase_owner2622K05P157 :
    (momentPanelPhase2622K05P157 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (27 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P157, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P157 :
    (momentPanelGrowth2622K05P157 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P157, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P157Input : RatPair2542 := (momentPanelPhase2622K05P157 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P157Expected : RatState2542 :=
  ((((6452457391427365264749402253596249828377246880607499622512904362367204781 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2649433896371661177812913 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P157_replay :
    compactExp2620 momentScalarAmp2622K05P157Input 20 = momentScalarAmp2622K05P157Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P157_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (27 / 40) 0) -
      (momentScalarAmp2622K05P157Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P157]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P157 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P157 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P157Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P157_replay] at h
  simpa only [momentPanelPhase_owner2622K05P157] using h

theorem momentScalarAmp2622K05P157_radius_le :
    (momentScalarAmp2622K05P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P157Expected]

def momentScalarGrow2622K05P157Input : RatPair2542 := (momentPanelGrowth2622K05P157 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P157Expected : RatState2542 :=
  ((((4444161279745551517150160827602780580694973613651908873077192029152504436069737869994903719541239 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5633636053394211485615903645288235428067485707429 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P157_replay :
    compactExp2620 momentScalarGrow2622K05P157Input 20 = momentScalarGrow2622K05P157Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P157_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P157Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P157]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P157 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P157 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P157Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P157_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P157] using h

theorem momentScalarGrow2622K05P157_radius_le :
    (momentScalarGrow2622K05P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P157Expected]

end ConnesWeilRH.Dev
