import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P077 : ℚ := ((-7430047974124228828992183228934333715793831646139 : ℚ) / 239777612374601260017792042867515182912301432832)

def momentPanelGrowth2622K02P077 : ℚ := ((559073195725671984652541168359480505822273238384289973 : ℚ) / 4598047856353373954267149869126122236929706881240268800)

theorem momentPanelPhase_owner2622K02P077 :
    (momentPanelPhase2622K02P077 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P077 :
    (momentPanelGrowth2622K02P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P077Input : RatPair2542 := (momentPanelPhase2622K02P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P077Expected : RatState2542 :=
  ((((4654665492107582138838983690514197783951560255938434532365678382371211407642283637 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((94410622038362002507197863385178317 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P077_replay :
    compactExp2620 momentScalarAmp2622K02P077Input 20 = momentScalarAmp2622K02P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K02P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P077_replay] at h
  simpa only [momentPanelPhase_owner2622K02P077] using h

theorem momentScalarAmp2622K02P077_radius_le :
    (momentScalarAmp2622K02P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P077Expected]

def momentScalarGrow2622K02P077Input : RatPair2542 := (momentPanelGrowth2622K02P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P077Expected : RatState2542 :=
  ((((150759320265938729900250083255216077191934134521798994143095707504295207128063497749174530031911 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3057761930634341139807383950701778567597096291545 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P077_replay :
    compactExp2620 momentScalarGrow2622K02P077Input 20 = momentScalarGrow2622K02P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P077] using h

theorem momentScalarGrow2622K02P077_radius_le :
    (momentScalarGrow2622K02P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P077Expected]

end ConnesWeilRH.Dev
