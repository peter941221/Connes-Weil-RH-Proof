import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P076 : ℚ := ((-85705310332895256786791990825218666450869781317638541 : ℚ) / 2802472207012787524451997415312556175044342133555200)

def momentPanelGrowth2622K01P076 : ℚ := ((6377255035296005619080216163979008805290443934245491 : ℚ) / 71450410136745634128578568259640554431673737098035200)

theorem momentPanelPhase_owner2622K01P076 :
    (momentPanelPhase2622K01P076 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P076 :
    (momentPanelGrowth2622K01P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P076Input : RatPair2542 := (momentPanelPhase2622K01P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P076Expected : RatState2542 :=
  ((((55841677145299359539569743500784032282378395370731355821822750738059569951361991843 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((141579600256233072424259195536438387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P076_replay :
    compactExp2620 momentScalarAmp2622K01P076Input 20 = momentScalarAmp2622K01P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K01P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P076_replay] at h
  simpa only [momentPanelPhase_owner2622K01P076] using h

theorem momentScalarAmp2622K01P076_radius_le :
    (momentScalarAmp2622K01P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P076Expected]

def momentScalarGrow2622K01P076Input : RatPair2542 := (momentPanelGrowth2622K01P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P076Expected : RatState2542 :=
  ((((583849971282646752464318955085708694753428092709545804125518047296348638267124838670420630170093 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((370058851770609100722108164911678263139882110173 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P076_replay :
    compactExp2620 momentScalarGrow2622K01P076Input 20 = momentScalarGrow2622K01P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P076] using h

theorem momentScalarGrow2622K01P076_radius_le :
    (momentScalarGrow2622K01P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P076Expected]

end ConnesWeilRH.Dev
