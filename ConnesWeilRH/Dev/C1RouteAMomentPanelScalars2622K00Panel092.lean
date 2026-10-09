import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P092 : ℚ := ((-14585570915221068543376282895455924344435572692640957 : ℚ) / 486862732935857034626602509898611780922882528378880)

def momentPanelGrowth2622K00P092 : ℚ := ((9625009961789292179604285540951338522551579026077934151 : ℚ) / 227948768468755239215981553906579407876530904016250470400)

theorem momentPanelPhase_owner2622K00P092 :
    (momentPanelPhase2622K00P092 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P092, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P092 :
    (momentPanelGrowth2622K00P092 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P092, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P092Input : RatPair2542 := (momentPanelPhase2622K00P092 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P092Expected : RatState2542 :=
  ((((208392541644759945785288968037880065847550563392636545662627307847424002138783296015 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((132088239016448189023028185614610295 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P092_replay :
    compactExp2620 momentScalarAmp2622K00P092Input 20 = momentScalarAmp2622K00P092Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P092_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 40) 0) -
      (momentScalarAmp2622K00P092Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P092]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P092 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P092 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P092Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P092_replay] at h
  simpa only [momentPanelPhase_owner2622K00P092] using h

theorem momentScalarAmp2622K00P092_radius_le :
    (momentScalarAmp2622K00P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [momentScalarAmp2622K00P092Expected]

def momentScalarGrow2622K00P092Input : RatPair2542 := (momentPanelGrowth2622K00P092 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P092Expected : RatState2542 :=
  ((((2228109115588919103964864863164638622321001429240500211579183885116328871184955912280660066315607 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2824463744013736197665842629144227948845492813847 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P092_replay :
    compactExp2620 momentScalarGrow2622K00P092Input 20 = momentScalarGrow2622K00P092Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P092_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P092Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P092]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P092 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P092 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P092Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P092_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P092] using h

theorem momentScalarGrow2622K00P092_radius_le :
    (momentScalarGrow2622K00P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P092Expected]

end ConnesWeilRH.Dev
