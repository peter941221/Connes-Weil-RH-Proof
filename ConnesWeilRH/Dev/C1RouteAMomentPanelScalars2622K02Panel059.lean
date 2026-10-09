import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P059 : ℚ := ((-118484305542293291011749390461487398307644946016600967 : ℚ) / 3451941269578634568327570445710548936855310984806400)

def momentPanelGrowth2622K02P059 : ℚ := ((1043813126602573445403566209709521249277300828668369253 : ℚ) / 3887038727773431332240105664297406143828186761055436800)

theorem momentPanelPhase_owner2622K02P059 :
    (momentPanelPhase2622K02P059 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-61 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P059, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P059 :
    (momentPanelGrowth2622K02P059 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P059, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P059Input : RatPair2542 := (momentPanelPhase2622K02P059 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P059Expected : RatState2542 :=
  ((((2647833928148262532564832343208009959854277030627957029848510224491131870553173991 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3356638144739102316556664427735809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P059_replay :
    compactExp2620 momentScalarAmp2622K02P059Input 20 = momentScalarAmp2622K02P059Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P059_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-61 / 200) 0) -
      (momentScalarAmp2622K02P059Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P059]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P059 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P059 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P059Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P059_replay] at h
  simpa only [momentPanelPhase_owner2622K02P059] using h

theorem momentScalarAmp2622K02P059_radius_le :
    (momentScalarAmp2622K02P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P059Expected]

def momentScalarGrow2622K02P059Input : RatPair2542 := (momentPanelGrowth2622K02P059 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P059Expected : RatState2542 :=
  ((((2793976079431236566601570048929498095650628253849365862063708008239394739016671263119452099268633 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1770892273537445303849309610042217220817146222127 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P059_replay :
    compactExp2620 momentScalarGrow2622K02P059Input 20 = momentScalarGrow2622K02P059Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P059_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P059Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P059]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P059 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P059 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P059Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P059_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P059] using h

theorem momentScalarGrow2622K02P059_radius_le :
    (momentScalarGrow2622K02P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P059Expected]

end ConnesWeilRH.Dev
