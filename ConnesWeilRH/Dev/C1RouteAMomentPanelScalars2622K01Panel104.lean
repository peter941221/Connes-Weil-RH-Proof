import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P104 : ℚ := ((-28519803388500881883011699345969196735147079750967399 : ℚ) / 931493206644544716372690337961213000760199584153600)

def momentPanelGrowth2622K01P104 : ℚ := ((523966771759628953426857825690354780112175840772513 : ℚ) / 5454976362714496314401795432385206648633267165593600)

theorem momentPanelPhase_owner2622K01P104 :
    (momentPanelPhase2622K01P104 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P104 :
    (momentPanelGrowth2622K01P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P104Input : RatPair2542 := (momentPanelPhase2622K01P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P104Expected : RatState2542 :=
  ((((53907083887276880930747985417153857774336185211369178634805326462666613714020490941 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((136674685191103950259169893165458901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P104_replay :
    compactExp2620 momentScalarAmp2622K01P104Input 20 = momentScalarAmp2622K01P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K01P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P104_replay] at h
  simpa only [momentPanelPhase_owner2622K01P104] using h

theorem momentScalarAmp2622K01P104_radius_le :
    (momentScalarAmp2622K01P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P104Expected]

def momentScalarGrow2622K01P104Input : RatPair2542 := (momentPanelGrowth2622K01P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P104Expected : RatState2542 :=
  ((((2351331676258202296194566915669724458061645622212740473589051884666661478397259823724880522819029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2980666737705537288217881493716576435747328552955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P104_replay :
    compactExp2620 momentScalarGrow2622K01P104Input 20 = momentScalarGrow2622K01P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P104] using h

theorem momentScalarGrow2622K01P104_radius_le :
    (momentScalarGrow2622K01P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P104Expected]

end ConnesWeilRH.Dev
