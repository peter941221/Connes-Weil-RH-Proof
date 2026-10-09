import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P172 : ℚ := ((-19229782303573519160744182487391176193 : ℚ) / 207286226149320071732740908143083520)

def momentPanelGrowth2622K05P172 : ℚ := ((16880569653602487540450179005781593210523 : ℚ) / 3271661179960393975819459750228760985600)

theorem momentPanelPhase_owner2622K05P172 :
    (momentPanelPhase2622K05P172 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P172 :
    (momentPanelGrowth2622K05P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P172Input : RatPair2542 := (momentPanelPhase2622K05P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P172Expected : RatState2542 :=
  ((((109758111820335257398481090718534708528997995830018654353 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258488594263 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P172_replay :
    compactExp2620 momentScalarAmp2622K05P172Input 20 = momentScalarAmp2622K05P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K05P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P172_replay] at h
  simpa only [momentPanelPhase_owner2622K05P172] using h

theorem momentScalarAmp2622K05P172_radius_le :
    (momentScalarAmp2622K05P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P172Expected]

def momentScalarGrow2622K05P172Input : RatPair2542 := (momentPanelGrowth2622K05P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P172Expected : RatState2542 :=
  ((((371876363779939882629800933809736460478779456830198347570822392848157801898333046406546698180414199 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((471406976141175731167667464369858362503407741161587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P172_replay :
    compactExp2620 momentScalarGrow2622K05P172Input 20 = momentScalarGrow2622K05P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P172] using h

theorem momentScalarGrow2622K05P172_radius_le :
    (momentScalarGrow2622K05P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P172Expected]

end ConnesWeilRH.Dev
