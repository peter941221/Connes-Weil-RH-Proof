import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P173 : ℚ := ((-28500160569023974469841174949255724707215842919385133 : ℚ) / 288089946772698001991615022933380593278857406054400)

def momentPanelGrowth2622K01P173 : ℚ := ((109796627687116469239264711562424844705982263308417 : ℚ) / 18875350736036319426995831945969573178661824102400)

theorem momentPanelPhase_owner2622K01P173 :
    (momentPanelPhase2622K01P173 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P173 :
    (momentPanelGrowth2622K01P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P173Input : RatPair2542 := (momentPanelPhase2622K01P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P173Expected : RatState2542 :=
  ((((58030545896112102065062154855544344664113850900125999 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((37778931862957161714191 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K01P173_replay :
    compactExp2620 momentScalarAmp2622K01P173Input 20 = momentScalarAmp2622K01P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K01P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P173_replay] at h
  simpa only [momentPanelPhase_owner2622K01P173] using h

theorem momentScalarAmp2622K01P173_radius_le :
    (momentScalarAmp2622K01P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P173Expected]

def momentScalarGrow2622K01P173Input : RatPair2542 := (momentPanelGrowth2622K01P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P173Expected : RatState2542 :=
  ((((179390730283386192499858227338659844732643745444928215717418381212686802709488384956997974119843515 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((909614021616476888577825808445088345828175303434013 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P173_replay :
    compactExp2620 momentScalarGrow2622K01P173Input 20 = momentScalarGrow2622K01P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P173] using h

theorem momentScalarGrow2622K01P173_radius_le :
    (momentScalarGrow2622K01P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P173Expected]

end ConnesWeilRH.Dev
