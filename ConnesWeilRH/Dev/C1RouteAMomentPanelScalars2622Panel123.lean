import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P123 : ℚ := ((-1783063586147790495131186581209272749623473470461775791 : ℚ) / 54061859003393430758678179265195756573960229722521600)

def momentPanelGrowth2622P123 : ℚ := ((1060550157254946671130632573530394093071637219150469797 : ℚ) / 3721136169597136908645831032351581553922624484854988800)

theorem momentPanelPhase_owner2622P123 :
    (momentPanelPhase2622P123 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (67 / 200) 0 := by
  norm_num [momentPanelPhase2622P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P123 :
    (momentPanelGrowth2622P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P123Input : RatPair2542 := (momentPanelPhase2622P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P123Expected : RatState2542 :=
  ((((10132937059828319907312105637335382145073397859945461607670500804487644077902712135 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6422713891085346146906075409752481 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P123_replay :
    compactExp2620 momentScalarAmp2622P123Input 20 = momentScalarAmp2622P123Expected := by
  decide +kernel

theorem momentScalarAmp2622P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P123]
  have h := compactExp_real_error2620 momentPanelPhase2622P123 20 hsmall
  change |Real.exp (momentPanelPhase2622P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P123_replay] at h
  simpa only [momentPanelPhase_owner2622P123] using h

theorem momentScalarAmp2622P123_radius_le :
    (momentScalarAmp2622P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P123Expected]

def momentScalarGrow2622P123Input : RatPair2542 := (momentPanelGrowth2622P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P123Expected : RatState2542 :=
  ((((2840374565208435438703063316898517860649013112159569036262687315511177267100466961403950566415769 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((450075192975209435584917436016266578774962996651 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P123_replay :
    compactExp2620 momentScalarGrow2622P123Input 20 = momentScalarGrow2622P123Expected := by
  decide +kernel

theorem momentScalarGrow2622P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P123_replay] at h
  simpa only [momentPanelGrowth_owner2622P123] using h

theorem momentScalarGrow2622P123_radius_le :
    (momentScalarGrow2622P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P123Expected]

end ConnesWeilRH.Dev
