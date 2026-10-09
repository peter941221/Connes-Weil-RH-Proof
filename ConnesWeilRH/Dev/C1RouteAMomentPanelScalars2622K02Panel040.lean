import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P040 : ℚ := ((-359985033160763329881816511308101982431893873948283979 : ℚ) / 8620290614405456489615835598281060724724513059635200)

def momentPanelGrowth2622K02P040 : ℚ := ((245865314757198472108434193019479024323263592877 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K02P040 :
    (momentPanelPhase2622K02P040 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P040 :
    (momentPanelGrowth2622K02P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P040Input : RatPair2542 := (momentPanelPhase2622K02P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P040Expected : RatState2542 :=
  ((((97556354832196833150306156999870607786307785001892779916881373111175014819433 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((989379584828479053194039500395 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P040_replay :
    compactExp2620 momentScalarAmp2622K02P040Input 20 = momentScalarAmp2622K02P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K02P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P040_replay] at h
  simpa only [momentPanelPhase_owner2622K02P040] using h

theorem momentScalarAmp2622K02P040_radius_le :
    (momentScalarAmp2622K02P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P040Expected]

def momentScalarGrow2622K02P040Input : RatPair2542 := (momentPanelGrowth2622K02P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P040Expected : RatState2542 :=
  ((((3792959803442931732700692574478042554839833327648236050809180697874404921854697976782839376210925 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1202036284613574299090233225387018981443562830393 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P040_replay :
    compactExp2620 momentScalarGrow2622K02P040Input 20 = momentScalarGrow2622K02P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P040] using h

theorem momentScalarGrow2622K02P040_radius_le :
    (momentScalarGrow2622K02P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P040Expected]

end ConnesWeilRH.Dev
