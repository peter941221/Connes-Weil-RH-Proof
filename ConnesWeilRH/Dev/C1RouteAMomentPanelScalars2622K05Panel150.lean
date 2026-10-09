import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P150 : ℚ := ((-796658632967910908239549897853277336643 : ℚ) / 17144720837966757009362611512069324800)

def momentPanelGrowth2622K05P150 : ℚ := ((12560347786629399370876013292239489160283 : ℚ) / 13327517602174062958649115359825205657600)

theorem momentPanelPhase_owner2622K05P150 :
    (momentPanelPhase2622K05P150 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P150 :
    (momentPanelGrowth2622K05P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P150Input : RatPair2542 := (momentPanelPhase2622K05P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P150Expected : RatState2542 :=
  ((((7052390851756053493933200205578274718034583853115462034360961622123606243865 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8941572597485921259628708709 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P150_replay :
    compactExp2620 momentScalarAmp2622K05P150Input 20 = momentScalarAmp2622K05P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K05P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P150_replay] at h
  simpa only [momentPanelPhase_owner2622K05P150] using h

theorem momentScalarAmp2622K05P150_radius_le :
    (momentScalarAmp2622K05P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P150Expected]

def momentScalarGrow2622K05P150Input : RatPair2542 := (momentPanelGrowth2622K05P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P150Expected : RatState2542 :=
  ((((5481429956217623096248518961971402002857109245894702602396775031811652194421027960487604315705327 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3474265864458621048622816687208107252072939778165 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P150_replay :
    compactExp2620 momentScalarGrow2622K05P150Input 20 = momentScalarGrow2622K05P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P150] using h

theorem momentScalarGrow2622K05P150_radius_le :
    (momentScalarGrow2622K05P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P150Expected]

end ConnesWeilRH.Dev
