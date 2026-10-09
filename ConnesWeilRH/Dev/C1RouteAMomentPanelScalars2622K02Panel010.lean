import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P010 : ℚ := ((-356195752818521280745845098838631587582305730111094959 : ℚ) / 4201531757787804697859382236865423782483529511731200)

def momentPanelGrowth2622K02P010 : ℚ := ((14430028082377802830834835635662989586345683437333 : ℚ) / 3853568770306091678857372117513636868233415884800)

theorem momentPanelPhase_owner2622K02P010 :
    (momentPanelPhase2622K02P010 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P010 :
    (momentPanelGrowth2622K02P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P010Input : RatPair2542 := (momentPanelPhase2622K02P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P010Expected : RatState2542 :=
  ((((324457205833822191356982313106212664236213116482991525595345 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807417420730917 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P010_replay :
    compactExp2620 momentScalarAmp2622K02P010Input 20 = momentScalarAmp2622K02P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K02P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P010_replay] at h
  simpa only [momentPanelPhase_owner2622K02P010] using h

theorem momentScalarAmp2622K02P010_radius_le :
    (momentScalarAmp2622K02P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P010Expected]

def momentScalarGrow2622K02P010Input : RatPair2542 := (momentPanelGrowth2622K02P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P010Expected : RatState2542 :=
  ((((90334282131558456926683159648991780101483696750367763854866893781435993664326051582625746171775261 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((114511898029074369993201143731807925007653806996755 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P010_replay :
    compactExp2620 momentScalarGrow2622K02P010Input 20 = momentScalarGrow2622K02P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P010] using h

theorem momentScalarGrow2622K02P010_radius_le :
    (momentScalarGrow2622K02P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P010Expected]

end ConnesWeilRH.Dev
