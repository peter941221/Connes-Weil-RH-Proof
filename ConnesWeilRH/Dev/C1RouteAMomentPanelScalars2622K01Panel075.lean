import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P075 : ℚ := ((-28570104319737513359319739432010608720162785209032601 : ℚ) / 931493206644544716372690337961213000760199584153600)

def momentPanelGrowth2622K01P075 : ℚ := ((523966771759628953426857825690354780112175840772513 : ℚ) / 5454976362714496314401795432385206648633267165593600)

theorem momentPanelPhase_owner2622K01P075 :
    (momentPanelPhase2622K01P075 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P075 :
    (momentPanelGrowth2622K01P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P075Input : RatPair2542 := (momentPanelPhase2622K01P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P075Expected : RatState2542 :=
  ((((12768321424809462442014284816959649974058062372270423539152402488134343695538576549 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((129489950127982614461733941398435403 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P075_replay :
    compactExp2620 momentScalarAmp2622K01P075Input 20 = momentScalarAmp2622K01P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K01P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P075_replay] at h
  simpa only [momentPanelPhase_owner2622K01P075] using h

theorem momentScalarAmp2622K01P075_radius_le :
    (momentScalarAmp2622K01P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P075Expected]

def momentScalarGrow2622K01P075Input : RatPair2542 := (momentPanelGrowth2622K01P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P075Expected : RatState2542 :=
  ((((2351331676258202296194566915669724458061645622212740473589051884666661478397259823724880522819029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2980666737705537288217881493716576435747328552955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P075_replay :
    compactExp2620 momentScalarGrow2622K01P075Input 20 = momentScalarGrow2622K01P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P075] using h

theorem momentScalarGrow2622K01P075_radius_le :
    (momentScalarGrow2622K01P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P075Expected]

end ConnesWeilRH.Dev
