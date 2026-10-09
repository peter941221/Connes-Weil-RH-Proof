import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P170 : ℚ := ((-29977322628351899468934674440355994025 : ℚ) / 380741393079749157198337801141092352)

def momentPanelGrowth2622K07P170 : ℚ := ((2010183212525556422117624363304324030075 : ℚ) / 479748799180217774575951719353204867072)

theorem momentPanelPhase_owner2622K07P170 :
    (momentPanelPhase2622K07P170 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P170 :
    (momentPanelGrowth2622K07P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P170Input : RatPair2542 := (momentPanelPhase2622K07P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P170Expected : RatState2542 :=
  ((((136717119364047557382445190105699715627929735025372468475845973 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((75557863731330654382739 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K07P170_replay :
    compactExp2620 momentScalarAmp2622K07P170Input 20 = momentScalarAmp2622K07P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K07P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P170_replay] at h
  simpa only [momentPanelPhase_owner2622K07P170] using h

theorem momentScalarAmp2622K07P170_radius_le :
    (momentScalarAmp2622K07P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P170Expected]

def momentScalarGrow2622K07P170Input : RatPair2542 := (momentPanelGrowth2622K07P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P170Expected : RatState2542 :=
  ((((141034333019481233861618784889210202842151388754054388616641022018754631857007754528910410391527165 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((89390771249231066265351932893794260194302039787249 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P170_replay :
    compactExp2620 momentScalarGrow2622K07P170Input 20 = momentScalarGrow2622K07P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P170] using h

theorem momentScalarGrow2622K07P170_radius_le :
    (momentScalarGrow2622K07P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P170Expected]

end ConnesWeilRH.Dev
