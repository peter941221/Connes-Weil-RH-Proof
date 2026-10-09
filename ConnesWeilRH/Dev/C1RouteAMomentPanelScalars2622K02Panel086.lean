import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P086 : ℚ := ((-114723769533054851987028394047061216653765125805858701 : ℚ) / 3801331504753053547210638851031785346241807358361600)

def momentPanelGrowth2622K02P086 : ℚ := ((4700706301832591535441803996428259865496798483253 : ℚ) / 72361458020192165969655098651089403414605253836800)

theorem momentPanelPhase_owner2622K02P086 :
    (momentPanelPhase2622K02P086 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-7 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P086, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P086 :
    (momentPanelGrowth2622K02P086 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P086, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P086Input : RatPair2542 := (momentPanelPhase2622K02P086 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P086Expected : RatState2542 :=
  ((((83485028145997808173806813127988014708191436664152278861704171324326535784233788375 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((211665784112883720910522826215872797 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P086_replay :
    compactExp2620 momentScalarAmp2622K02P086Input 20 = momentScalarAmp2622K02P086Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P086_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-7 / 200) 0) -
      (momentScalarAmp2622K02P086Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P086]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P086 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P086 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P086Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P086_replay] at h
  simpa only [momentPanelPhase_owner2622K02P086] using h

theorem momentScalarAmp2622K02P086_radius_le :
    (momentScalarAmp2622K02P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P086Expected]

def momentScalarGrow2622K02P086Input : RatPair2542 := (momentPanelGrowth2622K02P086 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P086Expected : RatState2542 :=
  ((((2279350004253939837639998306037279218413234927186954243478144760685097292969189167492850157975215 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2889419222017186476661422298838350957849652096177 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P086_replay :
    compactExp2620 momentScalarGrow2622K02P086Input 20 = momentScalarGrow2622K02P086Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P086_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P086Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P086]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P086 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P086 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P086Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P086_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P086] using h

theorem momentScalarGrow2622K02P086_radius_le :
    (momentScalarGrow2622K02P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P086Expected]

end ConnesWeilRH.Dev
