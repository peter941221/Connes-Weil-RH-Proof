import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P170 : ℚ := ((-799428827220328264513439754513087048563 : ℚ) / 9518534826993728929958445028527308800)

def momentPanelGrowth2622K18P170 : ℚ := ((49472014071916139501253758598092727225049 : ℚ) / 11993719979505444364398792983830121676800)

theorem momentPanelPhase_owner2622K18P170 :
    (momentPanelPhase2622K18P170 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P170 :
    (momentPanelGrowth2622K18P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P170Input : RatPair2542 := (momentPanelPhase2622K18P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P170Expected : RatState2542 :=
  ((((715660038733074630896173614929687450117193182587601559160315 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807541407938865 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K18P170_replay :
    compactExp2620 momentScalarAmp2622K18P170Input 20 = momentScalarAmp2622K18P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K18P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P170_replay] at h
  simpa only [momentPanelPhase_owner2622K18P170] using h

theorem momentScalarAmp2622K18P170_radius_le :
    (momentScalarAmp2622K18P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P170Expected]

def momentScalarGrow2622K18P170Input : RatPair2542 := (momentPanelGrowth2622K18P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P170Expected : RatState2542 :=
  ((((132125913401693637128255038637871313035896726614782407907020364350924426950415138233731686278825341 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((167488834570352106479578817606650642369519043219187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K18P170_replay :
    compactExp2620 momentScalarGrow2622K18P170Input 20 = momentScalarGrow2622K18P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P170] using h

theorem momentScalarGrow2622K18P170_radius_le :
    (momentScalarGrow2622K18P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P170Expected]

end ConnesWeilRH.Dev
