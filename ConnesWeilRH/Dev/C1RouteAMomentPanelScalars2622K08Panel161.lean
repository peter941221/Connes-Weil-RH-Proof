import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P161 : ℚ := ((-796658825374961371265536023880111302461 : ℚ) / 13218046338699793615286423663096627200)

def momentPanelGrowth2622K08P161 : ℚ := ((172555873576043314177351351935992796769 : ℚ) / 91880329625022249604002245688216780800)

theorem momentPanelPhase_owner2622K08P161 :
    (momentPanelPhase2622K08P161 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (143 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P161, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P161 :
    (momentPanelGrowth2622K08P161 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P161, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P161Input : RatPair2542 := (momentPanelPhase2622K08P161 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P161Expected : RatState2542 :=
  ((((14270346745305842060400286329510206714224822525311092212095350546130937 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2435942492651471388393311 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K08P161_replay :
    compactExp2620 momentScalarAmp2622K08P161Input 20 = momentScalarAmp2622K08P161Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P161_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (143 / 200) 0) -
      (momentScalarAmp2622K08P161Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P161]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P161 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P161 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P161Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P161_replay] at h
  simpa only [momentPanelPhase_owner2622K08P161] using h

theorem momentScalarAmp2622K08P161_radius_le :
    (momentScalarAmp2622K08P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P161Expected]

def momentScalarGrow2622K08P161Input : RatPair2542 := (momentPanelGrowth2622K08P161 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P161Expected : RatState2542 :=
  ((((13970934650252415591094376230233608937611865630949314907822074339148163828473413348752693052525795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2213778996904152684465068879701046454808895990599 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K08P161_replay :
    compactExp2620 momentScalarGrow2622K08P161Input 20 = momentScalarGrow2622K08P161Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P161_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P161Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P161]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P161 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P161 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P161Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P161_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P161] using h

theorem momentScalarGrow2622K08P161_radius_le :
    (momentScalarGrow2622K08P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P161Expected]

end ConnesWeilRH.Dev
