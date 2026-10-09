import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P093 : ℚ := ((-113635861299898728982297361064858005167474334034141299 : ℚ) / 3801331504753053547210638851031785346241807358361600)

def momentPanelGrowth2622K02P093 : ℚ := ((4700706301832591535441803996428259865496798483253 : ℚ) / 72361458020192165969655098651089403414605253836800)

theorem momentPanelPhase_owner2622K02P093 :
    (momentPanelPhase2622K02P093 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P093 :
    (momentPanelGrowth2622K02P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P093Input : RatPair2542 := (momentPanelPhase2622K02P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P093Expected : RatState2542 :=
  ((((222295116507006706548455687012261395438243313217951433659258734224032589480092073263 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((140900285783488547111445824845264445 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P093_replay :
    compactExp2620 momentScalarAmp2622K02P093Input 20 = momentScalarAmp2622K02P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K02P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P093_replay] at h
  simpa only [momentPanelPhase_owner2622K02P093] using h

theorem momentScalarAmp2622K02P093_radius_le :
    (momentScalarAmp2622K02P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P093Expected]

def momentScalarGrow2622K02P093Input : RatPair2542 := (momentPanelGrowth2622K02P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P093Expected : RatState2542 :=
  ((((2279350004253939837639998306037279218413234927186954243478144760685097292969189167492850157975215 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2889419222017186476661422298838350957849652096177 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P093_replay :
    compactExp2620 momentScalarGrow2622K02P093Input 20 = momentScalarGrow2622K02P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P093] using h

theorem momentScalarGrow2622K02P093_radius_le :
    (momentScalarGrow2622K02P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P093Expected]

end ConnesWeilRH.Dev
