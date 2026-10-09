import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P093 : ℚ := ((-809832221465478148331140270507110667189 : ℚ) / 27010084869182929503570554537587507200)

def momentPanelGrowth2622K28P093 : ℚ := ((20342696277367206601876801335242083 : ℚ) / 514159083452569845247062820100505600)

theorem momentPanelPhase_owner2622K28P093 :
    (momentPanelPhase2622K28P093 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P093 :
    (momentPanelGrowth2622K28P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P093Input : RatPair2542 := (momentPanelPhase2622K28P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P093Expected : RatState2542 :=
  ((((203388546682310748607169953627691963665316774400893268707612642552511097485489762591 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8057280798676297870096126339270677 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K28P093_replay :
    compactExp2620 momentScalarAmp2622K28P093Input 20 = momentScalarAmp2622K28P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K28P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P093_replay] at h
  simpa only [momentPanelPhase_owner2622K28P093] using h

theorem momentScalarAmp2622K28P093_radius_le :
    (momentScalarAmp2622K28P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P093Expected]

def momentScalarGrow2622K28P093Input : RatPair2542 := (momentPanelGrowth2622K28P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P093Expected : RatState2542 :=
  ((((2222191422991981272212181341251775149657134048287771982989753668351975623917184006985064500859029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((88030068277746249905119897331678003387307284099 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K28P093_replay :
    compactExp2620 momentScalarGrow2622K28P093Input 20 = momentScalarGrow2622K28P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P093] using h

theorem momentScalarGrow2622K28P093_radius_le :
    (momentScalarGrow2622K28P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P093Expected]

end ConnesWeilRH.Dev
