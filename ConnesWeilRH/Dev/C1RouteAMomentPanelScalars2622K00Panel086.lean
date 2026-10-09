import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P086 : ℚ := ((-1832026908122355857464360729409961760740880231068030149 : ℚ) / 60821304076048856755370221616508565539868917733785600)

def momentPanelGrowth2622K00P086 : ℚ := ((55885025776955105945506278001037969756289099210797 : ℚ) / 1157783328323074655514481578417430454633684061388800)

theorem momentPanelPhase_owner2622K00P086 :
    (momentPanelPhase2622K00P086 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-7 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P086, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P086 :
    (momentPanelGrowth2622K00P086 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P086, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P086Input : RatPair2542 := (momentPanelPhase2622K00P086 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P086Expected : RatState2542 :=
  ((((1382934801518952679171929091575292028134552317090555767315454526889974322714031223 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((28050055856135774076422602655999783 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K00P086_replay :
    compactExp2620 momentScalarAmp2622K00P086Input 20 = momentScalarAmp2622K00P086Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P086_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-7 / 200) 0) -
      (momentScalarAmp2622K00P086Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P086]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P086 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P086 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P086Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P086_replay] at h
  simpa only [momentPanelPhase_owner2622K00P086] using h

theorem momentScalarAmp2622K00P086_radius_le :
    (momentScalarAmp2622K00P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P086Expected]

def momentScalarGrow2622K00P086Input : RatPair2542 := (momentPanelGrowth2622K00P086 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P086Expected : RatState2542 :=
  ((((140101112379854470593272806080620661539916550207065795597224972112533760671532229653100105775663 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2841588016408927863522440529021809203564614528441 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P086_replay :
    compactExp2620 momentScalarGrow2622K00P086Input 20 = momentScalarGrow2622K00P086Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P086_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P086Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P086]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P086 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P086 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P086Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P086_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P086] using h

theorem momentScalarGrow2622K00P086_radius_le :
    (momentScalarGrow2622K00P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P086Expected]

end ConnesWeilRH.Dev
