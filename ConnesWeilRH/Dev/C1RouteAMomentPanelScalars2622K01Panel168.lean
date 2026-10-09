import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P168 : ℚ := ((-28491577025927182847854109353665742731419317100076263 : ℚ) / 365161322178819835568762465283653330643525723750400)

def momentPanelGrowth2622K01P168 : ℚ := ((564075778627690379915870102494822395850169227302369371 : ℚ) / 168059379208319352517532887245707430718285473329971200)

theorem momentPanelPhase_owner2622K01P168 :
    (momentPanelPhase2622K01P168 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P168 :
    (momentPanelGrowth2622K01P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P168Input : RatPair2542 := (momentPanelPhase2622K01P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P168Expected : RatState2542 :=
  ((((138964026013559267135521002630240046027760458251286792392330429 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819790800141679517 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P168_replay :
    compactExp2620 momentScalarAmp2622K01P168Input 20 = momentScalarAmp2622K01P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K01P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P168_replay] at h
  simpa only [momentPanelPhase_owner2622K01P168] using h

theorem momentScalarAmp2622K01P168_radius_le :
    (momentScalarAmp2622K01P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P168Expected]

def momentScalarGrow2622K01P168Input : RatPair2542 := (momentPanelGrowth2622K01P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P168Expected : RatState2542 :=
  ((((61272826510117143308348057213376779291365188345908236988771440244434998202876532935654514341414167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((77672286680077407687648771972353252688930368598375 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P168_replay :
    compactExp2620 momentScalarGrow2622K01P168Input 20 = momentScalarGrow2622K01P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P168] using h

theorem momentScalarGrow2622K01P168_radius_le :
    (momentScalarGrow2622K01P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P168Expected]

end ConnesWeilRH.Dev
