import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P173 : ℚ := ((-801648027651245209895971747307455759069 : ℚ) / 8188008756994179350147505344164659200)

def momentPanelGrowth2622K05P173 : ℚ := ((3127179559885600365453122674869636081 : ℚ) / 536469734016586682713404796515123200)

theorem momentPanelPhase_owner2622K05P173 :
    (momentPanelPhase2622K05P173 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P173 :
    (momentPanelGrowth2622K05P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P173Input : RatPair2542 := (momentPanelPhase2622K05P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P173Expected : RatState2542 :=
  ((((161392267423854632956352126632680534873033793112738013 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258350233443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P173_replay :
    compactExp2620 momentScalarAmp2622K05P173Input 20 = momentScalarAmp2622K05P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K05P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P173_replay] at h
  simpa only [momentPanelPhase_owner2622K05P173] using h

theorem momentScalarAmp2622K05P173_radius_le :
    (momentScalarAmp2622K05P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P173Expected]

def momentScalarGrow2622K05P173Input : RatPair2542 := (momentPanelGrowth2622K05P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P173Expected : RatState2542 :=
  ((((726407068967926623346987747774183995318943113025038683357416804891565062765858628342046526069405291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((230206309493942242712281693647411735405785103378047 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P173_replay :
    compactExp2620 momentScalarGrow2622K05P173Input 20 = momentScalarGrow2622K05P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P173] using h

theorem momentScalarGrow2622K05P173_radius_le :
    (momentScalarGrow2622K05P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P173Expected]

end ConnesWeilRH.Dev
