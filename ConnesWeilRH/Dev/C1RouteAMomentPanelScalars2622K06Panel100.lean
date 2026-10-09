import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P100 : ℚ := ((-59169261 : ℚ) / 1977950)

def momentPanelGrowth2622K06P100 : ℚ := ((87531547 : ℚ) / 813288675)

theorem momentPanelPhase_owner2622K06P100 :
    (momentPanelPhase2622K06P100 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P100 :
    (momentPanelGrowth2622K06P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P100Input : RatPair2542 := (momentPanelPhase2622K06P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P100Expected : RatState2542 :=
  ((((54433170275239033832073050837812456032855114655003092738234815995060297467491564611 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((69004209539847511426765491723066015 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P100_replay :
    compactExp2620 momentScalarAmp2622K06P100Input 20 = momentScalarAmp2622K06P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K06P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P100_replay] at h
  simpa only [momentPanelPhase_owner2622K06P100] using h

theorem momentScalarAmp2622K06P100_radius_le :
    (momentScalarAmp2622K06P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P100Expected]

def momentScalarGrow2622K06P100Input : RatPair2542 := (momentPanelGrowth2622K06P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P100Expected : RatState2542 :=
  ((((2378703320286727997538132301386926108943538039572395902906100291525517479467508428370722858717781 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3015364382226969073915065770609228851968272950815 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P100_replay :
    compactExp2620 momentScalarGrow2622K06P100Input 20 = momentScalarGrow2622K06P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P100] using h

theorem momentScalarGrow2622K06P100_radius_le :
    (momentScalarGrow2622K06P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P100Expected]

end ConnesWeilRH.Dev
