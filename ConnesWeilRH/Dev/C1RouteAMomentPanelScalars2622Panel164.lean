import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P164 : ℚ := ((-1778039737990936903088945494476509889622667041928695993 : ℚ) / 27097153794638271917820194101580334861308274304614400)

def momentPanelGrowth2622P164 : ℚ := ((265777288052226824140392549726901650393722424562759 : ℚ) / 111896219108147254674969620004840418692407335321600)

theorem momentPanelPhase_owner2622P164 :
    (momentPanelPhase2622P164 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (149 / 200) 0 := by
  norm_num [momentPanelPhase2622P164, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P164 :
    (momentPanelGrowth2622P164 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P164, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P164Input : RatPair2542 := (momentPanelPhase2622P164 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P164Expected : RatState2542 :=
  ((((67983681003257744498520473956026379314645252443560397864705500714255 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417937824176380751363837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P164_replay :
    compactExp2620 momentScalarAmp2622P164Input 20 = momentScalarAmp2622P164Expected := by
  decide +kernel

theorem momentScalarAmp2622P164_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (149 / 200) 0) -
      (momentScalarAmp2622P164Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P164]
  have h := compactExp_real_error2620 momentPanelPhase2622P164 20 hsmall
  change |Real.exp (momentPanelPhase2622P164 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P164Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P164_replay] at h
  simpa only [momentPanelPhase_owner2622P164] using h

theorem momentScalarAmp2622P164_radius_le :
    (momentScalarAmp2622P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P164Expected]

def momentScalarGrow2622P164Input : RatPair2542 := (momentPanelGrowth2622P164 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P164Expected : RatState2542 :=
  ((((22968903052873601448947509769600423589649365106752791024301628978296217136867268757994116460983843 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29116477787448466457644424670688138769930684089455 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P164_replay :
    compactExp2620 momentScalarGrow2622P164Input 20 = momentScalarGrow2622P164Expected := by
  decide +kernel

theorem momentScalarGrow2622P164_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P164Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P164]
  have h := compactExp_real_error2620 momentPanelGrowth2622P164 20 hsmall
  change |Real.exp (momentPanelGrowth2622P164 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P164Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P164_replay] at h
  simpa only [momentPanelGrowth_owner2622P164] using h

theorem momentScalarGrow2622P164_radius_le :
    (momentScalarGrow2622P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622P164Expected]

end ConnesWeilRH.Dev
