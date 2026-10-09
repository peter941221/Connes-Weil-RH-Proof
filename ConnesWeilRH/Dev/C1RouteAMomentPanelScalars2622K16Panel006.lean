import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P006 : ℚ := ((-821885510095032028192869407151234107051 : ℚ) / 8188008756994179350147505344164659200)

def momentPanelGrowth2622K16P006 : ℚ := ((3127917742239607189468034584443280201 : ℚ) / 536469734016586682713404796515123200)

theorem momentPanelPhase_owner2622K16P006 :
    (momentPanelPhase2622K16P006 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-167 / 200) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P006, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P006 :
    (momentPanelGrowth2622K16P006 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (-167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P006, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P006Input : RatPair2542 := (momentPanelPhase2622K16P006 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P006Expected : RatState2542 :=
  ((((27259035001795167002334829497820248419698193053653143 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614629174741121 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K16P006_replay :
    compactExp2620 momentScalarAmp2622K16P006Input 20 = momentScalarAmp2622K16P006Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P006_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-167 / 200) 0) -
      (momentScalarAmp2622K16P006Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P006]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P006 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P006 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P006Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P006_replay] at h
  simpa only [momentPanelPhase_owner2622K16P006] using h

theorem momentScalarAmp2622K16P006_radius_le :
    (momentScalarAmp2622K16P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P006Expected]

def momentScalarGrow2622K16P006Input : RatPair2542 := (momentPanelGrowth2622K16P006 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P006Expected : RatState2542 :=
  ((((727407293091206617195311560585840633337947967876301779514975398352833323479252588333330991402997261 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((461046582213688681314629306609855983804564289423395 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K16P006_replay :
    compactExp2620 momentScalarGrow2622K16P006Input 20 = momentScalarGrow2622K16P006Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P006_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P006Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P006]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P006 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P006 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P006Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P006_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P006] using h

theorem momentScalarGrow2622K16P006_radius_le :
    (momentScalarGrow2622K16P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P006Expected]

end ConnesWeilRH.Dev
