import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P161 : ℚ := ((-1775392740469686347665338867656988900882221472235784499 : ℚ) / 29764394282767169743541918921287551372180351195545600)

def momentPanelGrowth2622K00P161 : ℚ := ((390362107702705456484772650171771523799446882543269071 : ℚ) / 206896109130964273894018827388949934162261163009638400)

theorem momentPanelPhase_owner2622K00P161 :
    (momentPanelPhase2622K00P161 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (143 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P161, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P161 :
    (momentPanelGrowth2622K00P161 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P161, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P161Input : RatPair2542 := (momentPanelPhase2622K00P161 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P161Expected : RatState2542 :=
  ((((1661849282415476951145635085665752726695414289608362606376857646291809 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1225779932255941684361993 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P161_replay :
    compactExp2620 momentScalarAmp2622K00P161Input 20 = momentScalarAmp2622K00P161Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P161_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (143 / 200) 0) -
      (momentScalarAmp2622K00P161Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P161]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P161 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P161 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P161Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P161_replay] at h
  simpa only [momentPanelPhase_owner2622K00P161] using h

theorem momentScalarAmp2622K00P161_radius_le :
    (momentScalarAmp2622K00P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P161Expected]

def momentScalarGrow2622K00P161Input : RatPair2542 := (momentPanelGrowth2622K00P161 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P161Expected : RatState2542 :=
  ((((7046534210275113712283535111693608041029490170076484844764122093315243504561098436146016273987807 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((558282953027198342554146372155035217775983879227 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K00P161_replay :
    compactExp2620 momentScalarGrow2622K00P161Input 20 = momentScalarGrow2622K00P161Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P161_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P161Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P161]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P161 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P161 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P161Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P161_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P161] using h

theorem momentScalarGrow2622K00P161_radius_le :
    (momentScalarGrow2622K00P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P161Expected]

end ConnesWeilRH.Dev
