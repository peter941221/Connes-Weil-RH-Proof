import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P061 : ℚ := ((-219791696145085208655532413071063776523270568547308975 : ℚ) / 6713955834193501643362952660894514656921897110863872)

def momentPanelGrowth2622K03P061 : ℚ := ((537355580451294664999860646638992799286602459890007475 : ℚ) / 2554195802765365480897344266614767228029286178118172672)

theorem momentPanelPhase_owner2622K03P061 :
    (momentPanelPhase2622K03P061 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-57 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P061, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P061 :
    (momentPanelGrowth2622K03P061 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P061, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P061Input : RatPair2542 := (momentPanelPhase2622K03P061 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P061Expected : RatState2542 :=
  ((((6475437780001342581325804440974858353261895150954430146207525982173360679482151729 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((513053054126402306916604170871527 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K03P061_replay :
    compactExp2620 momentScalarAmp2622K03P061Input 20 = momentScalarAmp2622K03P061Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P061_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-57 / 200) 0) -
      (momentScalarAmp2622K03P061Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P061]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P061 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P061 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P061Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P061_replay] at h
  simpa only [momentPanelPhase_owner2622K03P061] using h

theorem momentScalarAmp2622K03P061_radius_le :
    (momentScalarAmp2622K03P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P061Expected]

def momentScalarGrow2622K03P061Input : RatPair2542 := (momentPanelGrowth2622K03P061 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P061Expected : RatState2542 :=
  ((((329515733761936958480233064440062666564094268902593143036358055563368755554489490232499300822491 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1670842935521506948468188810744718307436675170583 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P061_replay :
    compactExp2620 momentScalarGrow2622K03P061Input 20 = momentScalarGrow2622K03P061Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P061_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P061Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P061]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P061 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P061 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P061Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P061_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P061] using h

theorem momentScalarGrow2622K03P061_radius_le :
    (momentScalarGrow2622K03P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P061Expected]

end ConnesWeilRH.Dev
