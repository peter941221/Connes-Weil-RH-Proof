import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P098 : ℚ := ((-19774971 : ℚ) / 661850)

def momentPanelGrowth2622K06P098 : ℚ := ((233386561 : ℚ) / 2459664025)

theorem momentPanelPhase_owner2622K06P098 :
    (momentPanelPhase2622K06P098 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P098 :
    (momentPanelGrowth2622K06P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P098Input : RatPair2542 := (momentPanelPhase2622K06P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P098Expected : RatState2542 :=
  ((((56434657810788074982994665795466583664070899492323712368870755674799201815498776559 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((71541466335465155469983165828023797 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P098_replay :
    compactExp2620 momentScalarAmp2622K06P098Input 20 = momentScalarAmp2622K06P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K06P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P098_replay] at h
  simpa only [momentPanelPhase_owner2622K06P098] using h

theorem momentScalarAmp2622K06P098_radius_le :
    (momentScalarAmp2622K06P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P098Expected]

def momentScalarGrow2622K06P098Input : RatPair2542 := (momentPanelGrowth2622K06P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P098Expected : RatState2542 :=
  ((((2348588234929593063445184639216305973630652093337853757359945387114652561883046530648729934481085 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2977189016291886975261567242094792232594621935865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P098_replay :
    compactExp2620 momentScalarGrow2622K06P098Input 20 = momentScalarGrow2622K06P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P098] using h

theorem momentScalarGrow2622K06P098_radius_le :
    (momentScalarGrow2622K06P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P098Expected]

end ConnesWeilRH.Dev
