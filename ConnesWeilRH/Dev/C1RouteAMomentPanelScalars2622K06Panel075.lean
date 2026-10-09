import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P075 : ℚ := ((-20378537 : ℚ) / 652650)

def momentPanelGrowth2622K06P075 : ℚ := ((512881 : ℚ) / 3822025)

theorem momentPanelPhase_owner2622K06P075 :
    (momentPanelPhase2622K06P075 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P075 :
    (momentPanelGrowth2622K06P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P075Input : RatPair2542 := (momentPanelPhase2622K06P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P075Expected : RatState2542 :=
  ((((58756919000976360106759131270099123877454446112596978580172959530674869614116994667 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((74485461622427044042390961636589427 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P075_replay :
    compactExp2620 momentScalarAmp2622K06P075Input 20 = momentScalarAmp2622K06P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K06P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P075_replay] at h
  simpa only [momentPanelPhase_owner2622K06P075] using h

theorem momentScalarAmp2622K06P075_radius_le :
    (momentScalarAmp2622K06P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P075Expected]

def momentScalarGrow2622K06P075Input : RatPair2542 := (momentPanelGrowth2622K06P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P075Expected : RatState2542 :=
  ((((2442738530252311355729703122089272627395655148864427162796338046818754795144118047147596413441659 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3096538567797209250708944966326429253766308814047 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P075_replay :
    compactExp2620 momentScalarGrow2622K06P075Input 20 = momentScalarGrow2622K06P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P075] using h

theorem momentScalarGrow2622K06P075_radius_le :
    (momentScalarGrow2622K06P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P075Expected]

end ConnesWeilRH.Dev
