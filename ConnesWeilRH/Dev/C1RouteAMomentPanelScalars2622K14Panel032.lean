import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P032 : ℚ := ((-6619338770422458715221391270955164859 : ℚ) / 144816404570072926826983374182154240)

def momentPanelGrowth2622K14P032 : ℚ := ((749647096955729026352390107291789385563 : ℚ) / 930381509772467052101532745278790041600)

theorem momentPanelPhase_owner2622K14P032 :
    (momentPanelPhase2622K14P032 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-23 / 40) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P032, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P032 :
    (momentPanelGrowth2622K14P032 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (-23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P032, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P032Input : RatPair2542 := (momentPanelPhase2622K14P032 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P032Expected : RatState2542 :=
  ((((30106124829441355288321488493041035130344243300941160777264442405582239222955 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((38168128707860263798054848173 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K14P032_replay :
    compactExp2620 momentScalarAmp2622K14P032Input 20 = momentScalarAmp2622K14P032Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P032_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-23 / 40) 0) -
      (momentScalarAmp2622K14P032Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P032]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P032 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P032 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P032Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P032_replay] at h
  simpa only [momentPanelPhase_owner2622K14P032] using h

theorem momentScalarAmp2622K14P032_radius_le :
    (momentScalarAmp2622K14P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P032Expected]

def momentScalarGrow2622K14P032Input : RatPair2542 := (momentPanelGrowth2622K14P032 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P032Expected : RatState2542 :=
  ((((4781099128221750227210294016663611400764403704920969680794535204224401123067667880757546392839321 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1515189630615232203337614859885131052097250798213 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K14P032_replay :
    compactExp2620 momentScalarGrow2622K14P032Input 20 = momentScalarGrow2622K14P032Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P032_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P032Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P032]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P032 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P032 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P032Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P032_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P032] using h

theorem momentScalarGrow2622K14P032_radius_le :
    (momentScalarGrow2622K14P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P032Expected]

end ConnesWeilRH.Dev
