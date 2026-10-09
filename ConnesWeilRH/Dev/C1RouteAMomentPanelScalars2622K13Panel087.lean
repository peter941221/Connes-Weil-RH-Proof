import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P087 : ℚ := ((-6498742743200971703816153948009861677 : ℚ) / 216210486374926806719277698708930560)

def momentPanelGrowth2622K13P087 : ℚ := ((3393260730638501656065999346742133174889 : ℚ) / 101229588475584381875185948154873564364800)

theorem momentPanelPhase_owner2622K13P087 :
    (momentPanelPhase2622K13P087 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-1 / 40) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P087 :
    (momentPanelGrowth2622K13P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P087Input : RatPair2542 := (momentPanelPhase2622K13P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P087Expected : RatState2542 :=
  ((((188712278770983573247995832166673425441779623091688115620929812718988549703527568247 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((239228090843395776714887553377132441 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K13P087_replay :
    compactExp2620 momentScalarAmp2622K13P087Input 20 = momentScalarAmp2622K13P087Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622K13P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P087]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P087 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P087_replay] at h
  simpa only [momentPanelPhase_owner2622K13P087] using h

theorem momentScalarAmp2622K13P087_radius_le :
    (momentScalarAmp2622K13P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P087Expected]

def momentScalarGrow2622K13P087Input : RatPair2542 := (momentPanelGrowth2622K13P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P087Expected : RatState2542 :=
  ((((2208799809850717542624790082959912825091482464045225111038054872429952304900558880452472189747121 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1399993157616227729061469275233159506567808618577 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K13P087_replay :
    compactExp2620 momentScalarGrow2622K13P087Input 20 = momentScalarGrow2622K13P087Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P087_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P087] using h

theorem momentScalarGrow2622K13P087_radius_le :
    (momentScalarGrow2622K13P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P087Expected]

end ConnesWeilRH.Dev
