import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P030 : ℚ := ((-128032965390805363487894287460731834654328514300713069 : ℚ) / 2458576875455286491111003410973700321932919334502400)

def momentPanelGrowth2622K04P030 : ℚ := ((138957658883770951192231613180486795667340018527 : ℚ) / 142724769270595988105828596944949513638274662400)

theorem momentPanelPhase_owner2622K04P030 :
    (momentPanelPhase2622K04P030 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P030 :
    (momentPanelGrowth2622K04P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P030Input : RatPair2542 := (momentPanelPhase2622K04P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P030Expected : RatState2542 :=
  ((((6459050658849098956966846143833393090102070720017925465393471482285282411 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4245228773048106944359659 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K04P030_replay :
    compactExp2620 momentScalarAmp2622K04P030Input 20 = momentScalarAmp2622K04P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K04P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P030_replay] at h
  simpa only [momentPanelPhase_owner2622K04P030] using h

theorem momentScalarAmp2622K04P030_radius_le :
    (momentScalarAmp2622K04P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P030Expected]

def momentScalarGrow2622K04P030Input : RatPair2542 := (momentPanelGrowth2622K04P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P030Expected : RatState2542 :=
  ((((88358890101517977750822739411440994067536493632891450216829687111950948805576932638109546640671 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((7168518148659737239964015660657399245698153341061 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P030_replay :
    compactExp2620 momentScalarGrow2622K04P030Input 20 = momentScalarGrow2622K04P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P030] using h

theorem momentScalarGrow2622K04P030_radius_le :
    (momentScalarGrow2622K04P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P030Expected]

end ConnesWeilRH.Dev
