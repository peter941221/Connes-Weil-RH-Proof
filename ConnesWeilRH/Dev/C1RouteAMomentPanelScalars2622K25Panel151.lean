import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P151 : ℚ := ((-2385840274274336264150416980649917634923 : ℚ) / 50444380925242069511399208673450393600)

def momentPanelGrowth2622K25P151 : ℚ := ((798343920157073282055530186750491383083 : ℚ) / 800655217947510968069966126053431705600)

theorem momentPanelPhase_owner2622K25P151 :
    (momentPanelPhase2622K25P151 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (123 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P151, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P151 :
    (momentPanelGrowth2622K25P151 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P151, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P151Input : RatPair2542 := (momentPanelPhase2622K25P151 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P151Expected : RatState2542 :=
  ((((1537978337103185289431659144773897003412902246632781535369268031237586635773 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1950311565435875517573994329 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K25P151_replay :
    compactExp2620 momentScalarAmp2622K25P151Input 20 = momentScalarAmp2622K25P151Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P151_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (123 / 200) 0) -
      (momentScalarAmp2622K25P151Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P151]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P151 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P151 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P151Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P151_replay] at h
  simpa only [momentPanelPhase_owner2622K25P151] using h

theorem momentScalarAmp2622K25P151_radius_le :
    (momentScalarAmp2622K25P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P151Expected]

def momentScalarGrow2622K25P151Input : RatPair2542 := (momentPanelGrowth2622K25P151 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P151Expected : RatState2542 :=
  ((((723684722322909430644928757319798129181271468801017639234798024434089250633104581123006378317171 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3669514001093897807045485385813404648449967228481 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K25P151_replay :
    compactExp2620 momentScalarGrow2622K25P151Input 20 = momentScalarGrow2622K25P151Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P151_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P151Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P151]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P151 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P151 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P151Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P151_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P151] using h

theorem momentScalarGrow2622K25P151_radius_le :
    (momentScalarGrow2622K25P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P151Expected]

end ConnesWeilRH.Dev
