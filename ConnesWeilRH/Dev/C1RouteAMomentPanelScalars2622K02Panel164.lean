import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P164 : ℚ := ((-109021374687923725174622469571383846267809107248343457 : ℚ) / 1693572112164891994863762131348770928831767144038400)

def momentPanelGrowth2622K02P164 : ℚ := ((16727819590735324385063558853881660745328968614751 : ℚ) / 6993513694259203417185601250302526168275458457600)

theorem momentPanelPhase_owner2622K02P164 :
    (momentPanelPhase2622K02P164 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (149 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P164, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P164 :
    (momentPanelGrowth2622K02P164 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P164, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P164Input : RatPair2542 := (momentPanelPhase2622K02P164 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P164Expected : RatState2542 :=
  ((((235770164469115624810315288764496665728484028505274093167874700733555 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604537632942176018781605 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P164_replay :
    compactExp2620 momentScalarAmp2622K02P164Input 20 = momentScalarAmp2622K02P164Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P164_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (149 / 200) 0) -
      (momentScalarAmp2622K02P164Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P164]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P164 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P164 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P164Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P164_replay] at h
  simpa only [momentPanelPhase_owner2622K02P164] using h

theorem momentScalarAmp2622K02P164_radius_le :
    (momentScalarAmp2622K02P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P164Expected]

def momentScalarGrow2622K02P164Input : RatPair2542 := (momentPanelGrowth2622K02P164 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P164Expected : RatState2542 :=
  ((((2919441112807721578313590127178717923036443873012138413374661839466010646822087774187252886483183 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((29606582696252151696475203325937602575226412337187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P164_replay :
    compactExp2620 momentScalarGrow2622K02P164Input 20 = momentScalarGrow2622K02P164Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P164_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P164Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P164]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P164 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P164 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P164Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P164_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P164] using h

theorem momentScalarGrow2622K02P164_radius_le :
    (momentScalarGrow2622K02P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P164Expected]

end ConnesWeilRH.Dev
