import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P018 : ℚ := ((-1878361352857570947843873214133718648257609885204215501 : ℚ) / 29764394282767169743541918921287551372180351195545600)

def momentPanelGrowth2622K00P018 : ℚ := ((390362107702705456484772650171771523799446882543269071 : ℚ) / 206896109130964273894018827388949934162261163009638400)

theorem momentPanelPhase_owner2622K00P018 :
    (momentPanelPhase2622K00P018 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-143 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P018 :
    (momentPanelGrowth2622K00P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P018Input : RatPair2542 := (momentPanelPhase2622K00P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P018Expected : RatState2542 :=
  ((((418079593101170452549376281107572813252959149183273632766254053698611 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2418911660718209771348909 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P018_replay :
    compactExp2620 momentScalarAmp2622K00P018Input 20 = momentScalarAmp2622K00P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K00P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P018_replay] at h
  simpa only [momentPanelPhase_owner2622K00P018] using h

theorem momentScalarAmp2622K00P018_radius_le :
    (momentScalarAmp2622K00P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P018Expected]

def momentScalarGrow2622K00P018Input : RatPair2542 := (momentPanelGrowth2622K00P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P018Expected : RatState2542 :=
  ((((7046534210275113712283535111693608041029490170076484844764122093315243504561098436146016273987807 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((558282953027198342554146372155035217775983879227 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K00P018_replay :
    compactExp2620 momentScalarGrow2622K00P018Input 20 = momentScalarGrow2622K00P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P018] using h

theorem momentScalarGrow2622K00P018_radius_le :
    (momentScalarGrow2622K00P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P018Expected]

end ConnesWeilRH.Dev
