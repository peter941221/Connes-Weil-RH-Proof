import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P125 : ℚ := ((-1781169574731115743656817303046721979953284467010764027 : ℚ) / 53221495561928161580711060486383893837658068510310400)

def momentPanelGrowth2622P125 : ℚ := ((204128273799132385238702763194318188600264245980119 : ℚ) / 659959333107235849001351432273446551063382038937600)

theorem momentPanelPhase_owner2622P125 :
    (momentPanelPhase2622P125 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (71 / 200) 0 := by
  norm_num [momentPanelPhase2622P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P125 :
    (momentPanelGrowth2622P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P125Input : RatPair2542 := (momentPanelPhase2622P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P125Expected : RatState2542 :=
  ((((6237606855476486198029810081659737844016702378541837325869014782858612819066297463 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7907358449683923344727418204824983 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P125_replay :
    compactExp2620 momentScalarAmp2622P125Input 20 = momentScalarAmp2622P125Expected := by
  decide +kernel

theorem momentScalarAmp2622P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P125]
  have h := compactExp_real_error2620 momentPanelPhase2622P125 20 hsmall
  change |Real.exp (momentPanelPhase2622P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P125_replay] at h
  simpa only [momentPanelPhase_owner2622P125] using h

theorem momentScalarAmp2622P125_radius_le :
    (momentScalarAmp2622P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P125Expected]

def momentScalarGrow2622P125Input : RatPair2542 := (momentPanelGrowth2622P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P125Expected : RatState2542 :=
  ((((22736195917977721530724753225513329782320753792848225893236111440883249562746567609675162291265 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((461144702410847700535085865331806195236899326647 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P125_replay :
    compactExp2620 momentScalarGrow2622P125Input 20 = momentScalarGrow2622P125Expected := by
  decide +kernel

theorem momentScalarGrow2622P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P125_replay] at h
  simpa only [momentPanelGrowth_owner2622P125] using h

theorem momentScalarGrow2622P125_radius_le :
    (momentScalarGrow2622P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P125Expected]

end ConnesWeilRH.Dev
