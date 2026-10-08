import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P070 : ℚ := ((-362822601336108392135118793980906223904215069872076887 : ℚ) / 10983812793526526052648357163689424670574341468979200)

def momentPanelGrowth2622K04P070 : ℚ := ((96299764422435145917118889372140190353551575581 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K04P070 :
    (momentPanelPhase2622K04P070 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P070 :
    (momentPanelGrowth2622K04P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P070Input : RatPair2542 := (momentPanelPhase2622K04P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P070Expected : RatState2542 :=
  ((((9633272376813755284140178439755366729517372543655233233569547634709930930705942371 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12212008212479090671776115113451003 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P070_replay :
    compactExp2620 momentScalarAmp2622K04P070Input 20 = momentScalarAmp2622K04P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K04P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P070_replay] at h
  simpa only [momentPanelPhase_owner2622K04P070] using h

theorem momentScalarAmp2622K04P070_radius_le :
    (momentScalarAmp2622K04P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P070Expected]

def momentScalarGrow2622K04P070Input : RatPair2542 := (momentPanelGrowth2622K04P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P070Expected : RatState2542 :=
  ((((2674698610657980756081025620068523791866809268343554524688853093401439321971765511286729147101505 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3390582571987988716127264607433387357864070202029 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P070_replay :
    compactExp2620 momentScalarGrow2622K04P070Input 20 = momentScalarGrow2622K04P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P070] using h

theorem momentScalarGrow2622K04P070_radius_le :
    (momentScalarGrow2622K04P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P070Expected]

end ConnesWeilRH.Dev
