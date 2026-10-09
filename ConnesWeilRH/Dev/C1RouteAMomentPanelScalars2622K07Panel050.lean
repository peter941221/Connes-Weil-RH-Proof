import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P050 : ℚ := ((-35363324455796535512334184907586696025 : ℚ) / 912951821079568989122713674886152192)

def momentPanelGrowth2622K07P050 : ℚ := ((2509672023162730827467770829994625 : ℚ) / 5963028423473591104640491878088704)

theorem momentPanelPhase_owner2622K07P050 :
    (momentPanelPhase2622K07P050 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-79 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P050, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P050 :
    (momentPanelGrowth2622K07P050 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P050, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P050Input : RatPair2542 := (momentPanelPhase2622K07P050 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P050Expected : RatState2542 :=
  ((((32146768224801403872732492342010813639718805040090408624946666155163992675156323 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1273511807736108968783046702249 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K07P050_replay :
    compactExp2620 momentScalarAmp2622K07P050Input 20 = momentScalarAmp2622K07P050Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P050_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-79 / 200) 0) -
      (momentScalarAmp2622K07P050Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P050]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P050 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P050 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P050Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P050_replay] at h
  simpa only [momentPanelPhase_owner2622K07P050] using h

theorem momentScalarAmp2622K07P050_radius_le :
    (momentScalarAmp2622K07P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P050Expected]

def momentScalarGrow2622K07P050Input : RatPair2542 := (momentPanelGrowth2622K07P050 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P050Expected : RatState2542 :=
  ((((1626863170789619813849324898549304097689184192329217851361645575583518546189765400901966818768551 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1031146623593907225218544533451331604038334469627 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P050_replay :
    compactExp2620 momentScalarGrow2622K07P050Input 20 = momentScalarGrow2622K07P050Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P050_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P050Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P050]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P050 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P050 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P050Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P050_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P050] using h

theorem momentScalarGrow2622K07P050_radius_le :
    (momentScalarGrow2622K07P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P050Expected]

end ConnesWeilRH.Dev
