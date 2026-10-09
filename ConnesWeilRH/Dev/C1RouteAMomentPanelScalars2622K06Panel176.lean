import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P176 : ℚ := ((-19419239 : ℚ) / 167850)

def momentPanelGrowth2622K06P176 : ℚ := ((1310909761 : ℚ) / 147744025)

theorem momentPanelPhase_owner2622K06P176 :
    (momentPanelPhase2622K06P176 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (173 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P176, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P176 :
    (momentPanelGrowth2622K06P176 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P176, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P176Input : RatPair2542 := (momentPanelPhase2622K06P176 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P176Expected : RatState2542 :=
  ((((12143111338565137884612466491073592602493258073 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P176_replay :
    compactExp2620 momentScalarAmp2622K06P176Input 20 = momentScalarAmp2622K06P176Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P176_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (173 / 200) 0) -
      (momentScalarAmp2622K06P176Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P176]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P176 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P176 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P176Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P176_replay] at h
  simpa only [momentPanelPhase_owner2622K06P176] using h

theorem momentScalarAmp2622K06P176_radius_le :
    (momentScalarAmp2622K06P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P176Expected]

def momentScalarGrow2622K06P176Input : RatPair2542 := (momentPanelGrowth2622K06P176 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P176Expected : RatState2542 :=
  ((((7620720366305378677913245690307170436412378703853932108124888102372282312149622138663225256778645607 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2415082250590703750661666527107539376597176918078535 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K06P176_replay :
    compactExp2620 momentScalarGrow2622K06P176Input 20 = momentScalarGrow2622K06P176Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P176_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P176Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P176]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P176 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P176 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P176Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P176_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P176] using h

theorem momentScalarGrow2622K06P176_radius_le :
    (momentScalarGrow2622K06P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P176Expected]

end ConnesWeilRH.Dev
