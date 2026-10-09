import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K12
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K12P106 : ℚ := ((-2413720762687991506314404296987573185753 : ℚ) / 78920884008769014786621149479016857600)

def momentPanelGrowth2622K12P106 : ℚ := ((3941741940756499524353790268086824388083 : ℚ) / 31878377333142782975163141909051447705600)

theorem momentPanelPhase_owner2622K12P106 :
    (momentPanelPhase2622K12P106 : ℝ) = momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K12P106 :
    (momentPanelGrowth2622K12P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K12P106Input : RatPair2542 := (momentPanelPhase2622K12P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K12P106Expected : RatState2542 :=
  ((((111458119412508739278144607632470976887176821548784948423181915211283994920192543577 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((70647036536240933945114348772207509 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K12P106_replay :
    compactExp2620 momentScalarAmp2622K12P106Input 20 = momentScalarAmp2622K12P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K12P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K12P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K12P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K12P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K12P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K12P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K12P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K12P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K12P106_replay] at h
  simpa only [momentPanelPhase_owner2622K12P106] using h

theorem momentScalarAmp2622K12P106_radius_le :
    (momentScalarAmp2622K12P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarAmp2622K12P106Expected]

def momentScalarGrow2622K12P106Input : RatPair2542 := (momentPanelGrowth2622K12P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K12P106Expected : RatState2542 :=
  ((((2417123610843255791902161942943544884818926927097168093638091656430337585215094758383597654888305 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((95752119837267281323227333770316909153652816191 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K12P106_replay :
    compactExp2620 momentScalarGrow2622K12P106Input 20 = momentScalarGrow2622K12P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K12P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K12P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K12P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K12P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K12P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K12P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K12P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K12P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K12P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K12P106] using h

theorem momentScalarGrow2622K12P106_radius_le :
    (momentScalarGrow2622K12P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarGrow2622K12P106Expected]

end ConnesWeilRH.Dev
