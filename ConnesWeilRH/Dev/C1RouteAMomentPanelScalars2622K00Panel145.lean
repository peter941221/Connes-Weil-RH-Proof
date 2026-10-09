import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P145 : ℚ := ((-5310898846144263918046327025410424126742388549875390201 : ℚ) / 126415324436506443352999351514856242815801740178227200)

def momentPanelGrowth2622K00P145 : ℚ := ((103296438897151002743329000110852189209523706764506437 : ℚ) / 140091782727092033317252270988509085010675771428044800)

theorem momentPanelPhase_owner2622K00P145 :
    (momentPanelPhase2622K00P145 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (111 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P145 :
    (momentPanelGrowth2622K00P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P145Input : RatPair2542 := (momentPanelPhase2622K00P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P145Expected : RatState2542 :=
  ((((607017247340561054256389953618109336553980979748682320642363346040042673235053 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1539035634323366108308621605251 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P145_replay :
    compactExp2620 momentScalarAmp2622K00P145Input 20 = momentScalarAmp2622K00P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K00P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P145_replay] at h
  simpa only [momentPanelPhase_owner2622K00P145] using h

theorem momentScalarAmp2622K00P145_radius_le :
    (momentScalarAmp2622K00P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarAmp2622K00P145Expected]

def momentScalarGrow2622K00P145Input : RatPair2542 := (momentPanelGrowth2622K00P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P145Expected : RatState2542 :=
  ((((4465035474510346007541082059190864424725479969558337698170405026733743238645141419263120340954135 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2830050459587401106384847641278178632192583765659 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P145_replay :
    compactExp2620 momentScalarGrow2622K00P145Input 20 = momentScalarGrow2622K00P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P145] using h

theorem momentScalarGrow2622K00P145_radius_le :
    (momentScalarGrow2622K00P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P145Expected]

end ConnesWeilRH.Dev
