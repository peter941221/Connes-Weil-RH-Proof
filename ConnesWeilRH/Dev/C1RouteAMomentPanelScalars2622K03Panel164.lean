import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P164 : ℚ := ((-72836037452507542377358654843646647435837265083996775 : ℚ) / 1083886151785530876712807764063213394452330972184576)

def momentPanelGrowth2622K03P164 : ℚ := ((52680308666982551067504669633685383371296559211261 : ℚ) / 22379243821629450934993924000968083738481467064320)

theorem momentPanelPhase_owner2622K03P164 :
    (momentPanelPhase2622K03P164 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (149 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P164, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P164 :
    (momentPanelGrowth2622K03P164 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P164, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P164Input : RatPair2542 := (momentPanelPhase2622K03P164 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P164Expected : RatState2542 :=
  ((((3494579906408785043883769967526442115800444012680249876175012160417 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208934679995074745841111 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P164_replay :
    compactExp2620 momentScalarAmp2622K03P164Input 20 = momentScalarAmp2622K03P164Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P164_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (149 / 200) 0) -
      (momentScalarAmp2622K03P164Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P164]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P164 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P164 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P164Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P164_replay] at h
  simpa only [momentPanelPhase_owner2622K03P164] using h

theorem momentScalarAmp2622K03P164_radius_le :
    (momentScalarAmp2622K03P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P164Expected]

def momentScalarGrow2622K03P164Input : RatPair2542 := (momentPanelGrowth2622K03P164 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P164Expected : RatState2542 :=
  ((((2810796902223628656941275217946045185371589745892247149506935989174893613738322346542145700876145 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((445387547662510799355355798145677333033956287957 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K03P164_replay :
    compactExp2620 momentScalarGrow2622K03P164Input 20 = momentScalarGrow2622K03P164Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P164_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P164Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P164]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P164 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P164 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P164Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P164_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P164] using h

theorem momentScalarGrow2622K03P164_radius_le :
    (momentScalarGrow2622K03P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P164Expected]

end ConnesWeilRH.Dev
