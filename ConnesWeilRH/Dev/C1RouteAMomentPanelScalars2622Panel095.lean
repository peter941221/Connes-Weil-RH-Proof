import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P095 : ℚ := ((-1818798991845625142188257337104586618068805929227020967 : ℚ) / 60711691453249039036504945254054844313394722793062400)

def momentPanelGrowth2622P095 : ℚ := ((856607391734184746112577713619677670864970318965269151 : ℚ) / 14169900064485744391547248258556228368577583687034470400)

theorem momentPanelPhase_owner2622P095 :
    (momentPanelPhase2622P095 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (11 / 200) 0 := by
  norm_num [momentPanelPhase2622P095, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P095 :
    (momentPanelGrowth2622P095 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P095, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P095Input : RatPair2542 := (momentPanelPhase2622P095 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P095Expected : RatState2542 :=
  ((((208457648306121768984710463840295910745211784566063147762000295930031158165543537861 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((33032376601318834580184540165890059 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622P095_replay :
    compactExp2620 momentScalarAmp2622P095Input 20 = momentScalarAmp2622P095Expected := by
  decide +kernel

theorem momentScalarAmp2622P095_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (11 / 200) 0) -
      (momentScalarAmp2622P095Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P095]
  have h := compactExp_real_error2620 momentPanelPhase2622P095 20 hsmall
  change |Real.exp (momentPanelPhase2622P095 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P095Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P095_replay] at h
  simpa only [momentPanelPhase_owner2622P095] using h

theorem momentScalarAmp2622P095_radius_le :
    (momentScalarAmp2622P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [momentScalarAmp2622P095Expected]

def momentScalarGrow2622P095Input : RatPair2542 := (momentPanelGrowth2622P095 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P095Expected : RatState2542 :=
  ((((2269095872687513176936995065470362548668370004026826626295176092905955350732469275733512467957361 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2876420579156037919836517878512891866243929017901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P095_replay :
    compactExp2620 momentScalarGrow2622P095Input 20 = momentScalarGrow2622P095Expected := by
  decide +kernel

theorem momentScalarGrow2622P095_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P095Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P095]
  have h := compactExp_real_error2620 momentPanelGrowth2622P095 20 hsmall
  change |Real.exp (momentPanelGrowth2622P095 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P095Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P095_replay] at h
  simpa only [momentPanelGrowth_owner2622P095] using h

theorem momentScalarGrow2622P095_radius_le :
    (momentScalarGrow2622P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P095Expected]

end ConnesWeilRH.Dev
