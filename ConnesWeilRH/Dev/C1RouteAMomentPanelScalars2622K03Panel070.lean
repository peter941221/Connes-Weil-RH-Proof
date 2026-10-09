import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P070 : ℚ := ((-219631040296233314137051960117689225793657022714917425 : ℚ) / 7029640187856976673694948584761231789167578540146688)

def momentPanelGrowth2622K03P070 : ℚ := ((36492413416465886971420606247247925311809330875 : ℚ) / 274031556999544297163190906134303066185487351808)

theorem momentPanelPhase_owner2622K03P070 :
    (momentPanelPhase2622K03P070 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P070 :
    (momentPanelGrowth2622K03P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P070Input : RatPair2542 := (momentPanelPhase2622K03P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P070Expected : RatState2542 :=
  ((((28817712002795887805100280826314758221341523188719666947641646601596012498097145677 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((73063756826532635101866289009203673 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P070_replay :
    compactExp2620 momentScalarAmp2622K03P070Input 20 = momentScalarAmp2622K03P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K03P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P070_replay] at h
  simpa only [momentPanelPhase_owner2622K03P070] using h

theorem momentScalarAmp2622K03P070_radius_le :
    (momentScalarAmp2622K03P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P070Expected]

def momentScalarGrow2622K03P070Input : RatPair2542 := (momentPanelGrowth2622K03P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P070Expected : RatState2542 :=
  ((((2440242708579299531801877835356785975577799893782851274093189000072059953162065581935621302854563 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3093374741375963391392210217470041320325206127689 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P070_replay :
    compactExp2620 momentScalarGrow2622K03P070Input 20 = momentScalarGrow2622K03P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P070] using h

theorem momentScalarGrow2622K03P070_radius_le :
    (momentScalarGrow2622K03P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P070Expected]

end ConnesWeilRH.Dev
