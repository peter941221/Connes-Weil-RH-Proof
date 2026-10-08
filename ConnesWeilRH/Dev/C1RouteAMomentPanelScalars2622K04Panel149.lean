import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P149 : ℚ := ((-100326665442148217481431467651187387166910945539286931 : ℚ) / 2458576875455286491111003410973700321932919334502400)

def momentPanelGrowth2622K04P149 : ℚ := ((138957658883770951192231613180486795667340018527 : ℚ) / 142724769270595988105828596944949513638274662400)

theorem momentPanelPhase_owner2622K04P149 :
    (momentPanelPhase2622K04P149 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (119 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P149 :
    (momentPanelGrowth2622K04P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P149Input : RatPair2542 := (momentPanelPhase2622K04P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P149Expected : RatState2542 :=
  ((((4049754305122430066315765409582012423769307989098293973253842583220038673458037 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((320867230093817715025162146795 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K04P149_replay :
    compactExp2620 momentScalarAmp2622K04P149Input 20 = momentScalarAmp2622K04P149Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622K04P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P149]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P149 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P149_replay] at h
  simpa only [momentPanelPhase_owner2622K04P149] using h

theorem momentScalarAmp2622K04P149_radius_le :
    (momentScalarAmp2622K04P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P149Expected]

def momentScalarGrow2622K04P149Input : RatPair2542 := (momentPanelGrowth2622K04P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P149Expected : RatState2542 :=
  ((((88358890101517977750822739411440994067536493632891450216829687111950948805576932638109546640671 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((7168518148659737239964015660657399245698153341061 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P149_replay :
    compactExp2620 momentScalarGrow2622K04P149Input 20 = momentScalarGrow2622K04P149Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P149_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P149] using h

theorem momentScalarGrow2622K04P149_radius_le :
    (momentScalarGrow2622K04P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P149Expected]

end ConnesWeilRH.Dev
