import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P087 : ℚ := ((-14644461831396989820697413758869736048683078166879043 : ℚ) / 486862732935857034626602509898611780922882528378880)

def momentPanelGrowth2622P087 : ℚ := ((9625009961789292179604285540951338522551579026077934151 : ℚ) / 227948768468755239215981553906579407876530904016250470400)

theorem momentPanelPhase_owner2622P087 :
    (momentPanelPhase2622P087 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 40) 0 := by
  norm_num [momentPanelPhase2622P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P087 :
    (momentPanelGrowth2622P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P087Input : RatPair2542 := (momentPanelPhase2622P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P087Expected : RatState2542 :=
  ((((184650254685599063594699900405567497020782411960816536055161208505478265457726210571 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((117039360413021515551995356904077935 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P087_replay :
    compactExp2620 momentScalarAmp2622P087Input 20 = momentScalarAmp2622P087Expected := by
  decide +kernel

theorem momentScalarAmp2622P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P087]
  have h := compactExp_real_error2620 momentPanelPhase2622P087 20 hsmall
  change |Real.exp (momentPanelPhase2622P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P087_replay] at h
  simpa only [momentPanelPhase_owner2622P087] using h

theorem momentScalarAmp2622P087_radius_le :
    (momentScalarAmp2622P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P087Expected]

def momentScalarGrow2622P087Input : RatPair2542 := (momentPanelGrowth2622P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P087Expected : RatState2542 :=
  ((((2228109115588919103964864863164638622321001429240500211579183885116328871184955912280660066315607 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2824463744013736197665842629144227948845492813847 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P087_replay :
    compactExp2620 momentScalarGrow2622P087Input 20 = momentScalarGrow2622P087Expected := by
  decide +kernel

theorem momentScalarGrow2622P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P087_replay] at h
  simpa only [momentPanelGrowth_owner2622P087] using h

theorem momentScalarGrow2622P087_radius_le :
    (momentScalarGrow2622P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P087Expected]

end ConnesWeilRH.Dev
