import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P094 : ℚ := ((-340443018059714576025842423469383193463624285659887991 : ℚ) / 11394860129025842498393143522890879269852572496691200)

def momentPanelGrowth2622K02P094 : ℚ := ((538017673768921460329014913258744568279544349131493 : ℚ) / 7573975330882717300812006154077635840242321509580800)

theorem momentPanelPhase_owner2622K02P094 :
    (momentPanelPhase2622K02P094 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P094 :
    (momentPanelGrowth2622K02P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P094Input : RatPair2542 := (momentPanelPhase2622K02P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P094Expected : RatState2542 :=
  ((((226062642099323258219138221423384234752931246830521341087944474772810146410315895099 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8955519037807144634374200202102949 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K02P094_replay :
    compactExp2620 momentScalarAmp2622K02P094Input 20 = momentScalarAmp2622K02P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K02P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P094_replay] at h
  simpa only [momentPanelPhase_owner2622K02P094] using h

theorem momentScalarAmp2622K02P094_radius_le :
    (momentScalarAmp2622K02P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P094Expected]

def momentScalarGrow2622K02P094Input : RatPair2542 := (momentPanelGrowth2622K02P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P094Expected : RatState2542 :=
  ((((2293235944088600273866808721201433038238248891640058584079993175245737210909715067385902858033767 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2907021724054713645255377469892775772001662336135 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P094_replay :
    compactExp2620 momentScalarGrow2622K02P094Input 20 = momentScalarGrow2622K02P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P094] using h

theorem momentScalarGrow2622K02P094_radius_le :
    (momentScalarGrow2622K02P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P094Expected]

end ConnesWeilRH.Dev
