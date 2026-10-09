import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K22
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K22P018 : ℚ := ((-825933942917172262650244079001168697539 : ℚ) / 13218046338699793615286423663096627200)

def momentPanelGrowth2622K22P018 : ℚ := ((172555873576043314177351351935992796769 : ℚ) / 91880329625022249604002245688216780800)

theorem momentPanelPhase_owner2622K22P018 :
    (momentPanelPhase2622K22P018 : ℝ) = momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-143 / 200) 0 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K22P018 :
    (momentPanelGrowth2622K22P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K22P018Input : RatPair2542 := (momentPanelPhase2622K22P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K22P018Expected : RatState2542 :=
  ((((778997493684622102375668985859164557424121890985548405198311628341215 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1209913375102461254120245 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K22P018_replay :
    compactExp2620 momentScalarAmp2622K22P018Input 20 = momentScalarAmp2622K22P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K22P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K22P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K22P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K22P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K22P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K22P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K22P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K22P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K22P018_replay] at h
  simpa only [momentPanelPhase_owner2622K22P018] using h

theorem momentScalarAmp2622K22P018_radius_le :
    (momentScalarAmp2622K22P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarAmp2622K22P018Expected]

def momentScalarGrow2622K22P018Input : RatPair2542 := (momentPanelGrowth2622K22P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K22P018Expected : RatState2542 :=
  ((((13970934650252415591094376230233608937611865630949314907822074339148163828473413348752693052525795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2213778996904152684465068879701046454808895990599 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K22P018_replay :
    compactExp2620 momentScalarGrow2622K22P018Input 20 = momentScalarGrow2622K22P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K22P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K22P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K22P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K22P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K22P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K22P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K22P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K22P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K22P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K22P018] using h

theorem momentScalarGrow2622K22P018_radius_le :
    (momentScalarGrow2622K22P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarGrow2622K22P018Expected]

end ConnesWeilRH.Dev
