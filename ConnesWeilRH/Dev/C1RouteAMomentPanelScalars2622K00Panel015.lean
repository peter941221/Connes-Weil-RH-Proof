import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P015 : ℚ := ((-1875714355336320392420266587314197659517164315511304007 : ℚ) / 27097153794638271917820194101580334861308274304614400)

def momentPanelGrowth2622K00P015 : ℚ := ((265777288052226824140392549726901650393722424562759 : ℚ) / 111896219108147254674969620004840418692407335321600)

theorem momentPanelPhase_owner2622K00P015 :
    (momentPanelPhase2622K00P015 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-149 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P015, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P015 :
    (momentPanelGrowth2622K00P015 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P015, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P015Input : RatPair2542 := (momentPanelPhase2622K00P015 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P015Expected : RatState2542 :=
  ((((1849027252101212941591819152048874514756356761909995318636913393741 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208926991652254002777099 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P015_replay :
    compactExp2620 momentScalarAmp2622K00P015Input 20 = momentScalarAmp2622K00P015Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P015_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-149 / 200) 0) -
      (momentScalarAmp2622K00P015Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P015]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P015 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P015 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P015Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P015_replay] at h
  simpa only [momentPanelPhase_owner2622K00P015] using h

theorem momentScalarAmp2622K00P015_radius_le :
    (momentScalarAmp2622K00P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P015Expected]

def momentScalarGrow2622K00P015Input : RatPair2542 := (momentPanelGrowth2622K00P015 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P015Expected : RatState2542 :=
  ((((22968903052873601448947509769600423589649365106752791024301628978296217136867268757994116460983843 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29116477787448466457644424670688138769930684089455 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P015_replay :
    compactExp2620 momentScalarGrow2622K00P015Input 20 = momentScalarGrow2622K00P015Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P015_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P015Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P015]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P015 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P015 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P015Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P015_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P015] using h

theorem momentScalarGrow2622K00P015_radius_le :
    (momentScalarGrow2622K00P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622K00P015Expected]

end ConnesWeilRH.Dev
