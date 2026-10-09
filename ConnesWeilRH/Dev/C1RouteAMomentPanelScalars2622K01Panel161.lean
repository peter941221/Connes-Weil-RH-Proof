import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P161 : ℚ := ((-28483035207925714278259704778232355760505523831386837 : ℚ) / 465068660668237027242842483145117990190317987430400)

def momentPanelGrowth2622K01P161 : ℚ := ((6027220845898433646029104263563567220277852158650073 : ℚ) / 3232751705171316779594044177952342721285330672025600)

theorem momentPanelPhase_owner2622K01P161 :
    (momentPanelPhase2622K01P161 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (143 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P161, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P161 :
    (momentPanelGrowth2622K01P161 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P161, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P161Input : RatPair2542 := (momentPanelPhase2622K01P161 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P161Expected : RatState2542 :=
  ((((5386686520173010886650869829191537852156556029359798827541477048344145 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((303085059309274176602493 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P161_replay :
    compactExp2620 momentScalarAmp2622K01P161Input 20 = momentScalarAmp2622K01P161Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P161_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (143 / 200) 0) -
      (momentScalarAmp2622K01P161Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P161]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P161 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P161 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P161Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P161_replay] at h
  simpa only [momentPanelPhase_owner2622K01P161] using h

theorem momentScalarAmp2622K01P161_radius_le :
    (momentScalarAmp2622K01P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P161Expected]

def momentScalarGrow2622K01P161Input : RatPair2542 := (momentPanelGrowth2622K01P161 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P161Expected : RatState2542 :=
  ((((13781858903281555693950529894719255792641489183012719276590741963374252820131698177212397628425821 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((17470550647403014305427641473186095141702550693783 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P161_replay :
    compactExp2620 momentScalarGrow2622K01P161Input 20 = momentScalarGrow2622K01P161Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P161_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P161Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P161Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P161 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P161]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P161 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P161 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P161Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P161Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P161_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P161] using h

theorem momentScalarGrow2622K01P161_radius_le :
    (momentScalarGrow2622K01P161Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P161Expected]

end ConnesWeilRH.Dev
