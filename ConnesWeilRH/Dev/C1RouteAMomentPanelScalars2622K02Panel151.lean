import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P151 : ℚ := ((-324688707789354689265637228340723118962717659036707693 : ℚ) / 7099415473057985640360126069235678707395058257100800)

def momentPanelGrowth2622K02P151 : ℚ := ((115218649517371494538205191128030478734318052427214253 : ℚ) / 112682204412520426781468418088216255664013313887436800)

theorem momentPanelPhase_owner2622K02P151 :
    (momentPanelPhase2622K02P151 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (123 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P151, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P151 :
    (momentPanelGrowth2622K02P151 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P151, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P151Input : RatPair2542 := (momentPanelPhase2622K02P151 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P151Expected : RatState2542 :=
  ((((29331049563684199876692459405603446438169261966067424752800510594394618553695 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18592781088354517746339207761 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P151_replay :
    compactExp2620 momentScalarAmp2622K02P151Input 20 = momentScalarAmp2622K02P151Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P151_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (123 / 200) 0) -
      (momentScalarAmp2622K02P151Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P151]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P151 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P151 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P151Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P151_replay] at h
  simpa only [momentPanelPhase_owner2622K02P151] using h

theorem momentScalarAmp2622K02P151_radius_le :
    (momentScalarAmp2622K02P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P151Expected]

def momentScalarGrow2622K02P151Input : RatPair2542 := (momentPanelGrowth2622K02P151 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P151Expected : RatState2542 :=
  ((((5938393093730115348882231646566753571098954872872296624489227738049470109970561117218279367964963 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7527800228985971893395654080394422617724576253839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P151_replay :
    compactExp2620 momentScalarGrow2622K02P151Input 20 = momentScalarGrow2622K02P151Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P151_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P151Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P151]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P151 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P151 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P151Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P151_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P151] using h

theorem momentScalarGrow2622K02P151_radius_le :
    (momentScalarGrow2622K02P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P151Expected]

end ConnesWeilRH.Dev
