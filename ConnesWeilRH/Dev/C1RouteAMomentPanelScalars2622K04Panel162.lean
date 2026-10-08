import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P162 : ℚ := ((-814271872410694753670542227478563552051437129507401 : ℚ) / 14443746650184313996309854010828890780193395834880)

def momentPanelGrowth2622K04P162 : ℚ := ((2182079840835043744848915007120910589111938330821703669 : ℚ) / 1038001137538419160708700610945590740464221136145612800)

theorem momentPanelPhase_owner2622K04P162 :
    (momentPanelPhase2622K04P162 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P162 :
    (momentPanelGrowth2622K04P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P162Input : RatPair2542 := (momentPanelPhase2622K04P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P162Expected : RatState2542 :=
  ((((701579936047813890204295268173784979817500461403360200639676623230393491 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3307257682801424013326715 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P162_replay :
    compactExp2620 momentScalarAmp2622K04P162Input 20 = momentScalarAmp2622K04P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K04P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P162_replay] at h
  simpa only [momentPanelPhase_owner2622K04P162] using h

theorem momentScalarAmp2622K04P162_radius_le :
    (momentScalarAmp2622K04P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P162Expected]

def momentScalarGrow2622K04P162Input : RatPair2542 := (momentPanelGrowth2622K04P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P162Expected : RatState2542 :=
  ((((17481145959898549294828833004703759399876243425082259811298448437261277127123203208614043092711065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11079970371130327457840981050001801586198078635765 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P162_replay :
    compactExp2620 momentScalarGrow2622K04P162Input 20 = momentScalarGrow2622K04P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P162] using h

theorem momentScalarGrow2622K04P162_radius_le :
    (momentScalarGrow2622K04P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P162Expected]

end ConnesWeilRH.Dev
