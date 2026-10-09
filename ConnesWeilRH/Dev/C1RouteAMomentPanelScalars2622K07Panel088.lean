import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P088 : ℚ := ((-97748482620636944021249993328885135975 : ℚ) / 3244455369838535807696298104716263424)

def momentPanelGrowth2622K07P088 : ℚ := ((7831665760458884281616762741727427025 : ℚ) / 84442445504809523632814005485614137344)

theorem momentPanelPhase_owner2622K07P088 :
    (momentPanelPhase2622K07P088 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P088 :
    (momentPanelGrowth2622K07P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P088Input : RatPair2542 := (momentPanelPhase2622K07P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P088Expected : RatState2542 :=
  ((((175888404320629347903390560431639984537225586031833867468187892084127043936231761409 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((55742861918093508158945532364217049 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P088_replay :
    compactExp2620 momentScalarAmp2622K07P088Input 20 = momentScalarAmp2622K07P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K07P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P088_replay] at h
  simpa only [momentPanelPhase_owner2622K07P088] using h

theorem momentScalarAmp2622K07P088_radius_le :
    (momentScalarAmp2622K07P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P088Expected]

def momentScalarGrow2622K07P088Input : RatPair2542 := (momentPanelGrowth2622K07P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P088Expected : RatState2542 :=
  ((((2343567772976498908697837798172554454491867361500091450378151624056461285904359827259102034637361 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2970824831322393080606911888073070155382165992273 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P088_replay :
    compactExp2620 momentScalarGrow2622K07P088Input 20 = momentScalarGrow2622K07P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P088] using h

theorem momentScalarGrow2622K07P088_radius_le :
    (momentScalarGrow2622K07P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P088Expected]

end ConnesWeilRH.Dev
