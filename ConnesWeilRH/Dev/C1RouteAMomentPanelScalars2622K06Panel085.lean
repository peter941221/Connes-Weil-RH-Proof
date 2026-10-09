import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P085 : ℚ := ((-60359271 : ℚ) / 1995950)

def momentPanelGrowth2622K06P085 : ℚ := ((93067 : ℚ) / 1326675)

theorem momentPanelPhase_owner2622K06P085 :
    (momentPanelPhase2622K06P085 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P085, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P085 :
    (momentPanelGrowth2622K06P085 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P085, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P085Input : RatPair2542 := (momentPanelPhase2622K06P085 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P085Expected : RatState2542 :=
  ((((157092056130613847886519367273818037061205953027671856715212890046854373281338234691 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((199143582454454025579501985901588717 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P085_replay :
    compactExp2620 momentScalarAmp2622K06P085Input 20 = momentScalarAmp2622K06P085Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P085_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 200) 0) -
      (momentScalarAmp2622K06P085Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P085]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P085 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P085 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P085Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P085_replay] at h
  simpa only [momentPanelPhase_owner2622K06P085] using h

theorem momentScalarAmp2622K06P085_radius_le :
    (momentScalarAmp2622K06P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P085Expected]

def momentScalarGrow2622K06P085Input : RatPair2542 := (momentPanelGrowth2622K06P085 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P085Expected : RatState2542 :=
  ((((572802129875298579893001528028585653788082493172391403984992913219547865672731027502128651063421 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((726112915170900079779528582726389685283306550369 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P085_replay :
    compactExp2620 momentScalarGrow2622K06P085Input 20 = momentScalarGrow2622K06P085Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P085_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P085Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P085]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P085 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P085 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P085Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P085_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P085] using h

theorem momentScalarGrow2622K06P085_radius_le :
    (momentScalarGrow2622K06P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P085Expected]

end ConnesWeilRH.Dev
