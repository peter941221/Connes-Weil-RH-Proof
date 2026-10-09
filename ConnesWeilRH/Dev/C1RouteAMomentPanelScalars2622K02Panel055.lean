import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P055 : ℚ := ((-356727750552979082987562604266642329980342243514089389 : ℚ) / 10058956288653064049722587855486151822198321656627200)

def momentPanelGrowth2622K02P055 : ℚ := ((1838152723069663381588535692300020689198884576023493 : ℚ) / 5861278099635565443542062990738241676583025560780800)

theorem momentPanelPhase_owner2622K02P055 :
    (momentPanelPhase2622K02P055 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P055 :
    (momentPanelGrowth2622K02P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P055Input : RatPair2542 := (momentPanelPhase2622K02P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P055Expected : RatState2542 :=
  ((((847055527192107216384966941245017542252913633929101543589999811513420204273628603 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1073806766294694892664430584045165 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P055_replay :
    compactExp2620 momentScalarAmp2622K02P055Input 20 = momentScalarAmp2622K02P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K02P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P055_replay] at h
  simpa only [momentPanelPhase_owner2622K02P055] using h

theorem momentScalarAmp2622K02P055_radius_le :
    (momentScalarAmp2622K02P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P055Expected]

def momentScalarGrow2622K02P055Input : RatPair2542 := (momentPanelGrowth2622K02P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P055Expected : RatState2542 :=
  ((((2922789272960894562865433782129213318774955245717002123501945868336956182824904395085895114707151 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((231567154255663843029104594387018985872973647315 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K02P055_replay :
    compactExp2620 momentScalarGrow2622K02P055Input 20 = momentScalarGrow2622K02P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P055] using h

theorem momentScalarGrow2622K02P055_radius_le :
    (momentScalarGrow2622K02P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P055Expected]

end ConnesWeilRH.Dev
