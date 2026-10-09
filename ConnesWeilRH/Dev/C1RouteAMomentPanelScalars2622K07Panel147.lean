import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P147 : ℚ := ((-1163617396380958735730080604273114875 : ℚ) / 28963280914014585365396674836430848)

def momentPanelGrowth2622K07P147 : ℚ := ((32414105188214517697364392587117069025 : ℚ) / 37215260390898682084061309811151601664)

theorem momentPanelPhase_owner2622K07P147 :
    (momentPanelPhase2622K07P147 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P147 :
    (momentPanelGrowth2622K07P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P147Input : RatPair2542 := (momentPanelPhase2622K07P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P147Expected : RatState2542 :=
  ((((3806484935632909446540065419821434141031437847067042254176321715748888869499241 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1206369751075228298092203407767 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P147_replay :
    compactExp2620 momentScalarAmp2622K07P147Input 20 = momentScalarAmp2622K07P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K07P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P147_replay] at h
  simpa only [momentPanelPhase_owner2622K07P147] using h

theorem momentScalarAmp2622K07P147_radius_le :
    (momentScalarAmp2622K07P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P147Expected]

def momentScalarGrow2622K07P147Input : RatPair2542 := (momentPanelGrowth2622K07P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P147Expected : RatState2542 :=
  ((((5103458581956976826339637130822796248040384274209272158455155373459477843247556259951058911893059 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6469396960912814770406296469244963478018566165417 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P147_replay :
    compactExp2620 momentScalarGrow2622K07P147Input 20 = momentScalarGrow2622K07P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P147] using h

theorem momentScalarGrow2622K07P147_radius_le :
    (momentScalarGrow2622K07P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P147Expected]

end ConnesWeilRH.Dev
