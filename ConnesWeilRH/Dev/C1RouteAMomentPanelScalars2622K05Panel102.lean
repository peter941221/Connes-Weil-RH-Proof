import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P102 : ℚ := ((-51622431952805207236431764354238091 : ℚ) / 1703722406706740315611569108025344)

def momentPanelGrowth2622K05P102 : ℚ := ((3097767741539374204275576775449374607643 : ℚ) / 32671095030091904862012696278314097049600)

theorem momentPanelPhase_owner2622K05P102 :
    (momentPanelPhase2622K05P102 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (1 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P102, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P102 :
    (momentPanelGrowth2622K05P102 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P102, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P102Input : RatPair2542 := (momentPanelPhase2622K05P102 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P102Expected : RatState2542 :=
  ((((37026001510196044301453717807058097932607889341405421314396333877628335442032718899 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((187749557313825129992048663816459157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P102_replay :
    compactExp2620 momentScalarAmp2622K05P102Input 20 = momentScalarAmp2622K05P102Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P102_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (1 / 8) 0) -
      (momentScalarAmp2622K05P102Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P102]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P102 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P102 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P102Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P102_replay] at h
  simpa only [momentPanelPhase_owner2622K05P102] using h

theorem momentScalarAmp2622K05P102_radius_le :
    (momentScalarAmp2622K05P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P102Expected]

def momentScalarGrow2622K05P102Input : RatPair2542 := (momentPanelGrowth2622K05P102 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P102Expected : RatState2542 :=
  ((((2348426719594993480262601959507901673230110657760928429382922567905247747672064580919257659200883 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((372123033936852054099951466642402141427375892451 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K05P102_replay :
    compactExp2620 momentScalarGrow2622K05P102Input 20 = momentScalarGrow2622K05P102Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P102_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P102Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P102Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P102 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P102]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P102 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P102 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P102Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P102Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P102_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P102] using h

theorem momentScalarGrow2622K05P102_radius_le :
    (momentScalarGrow2622K05P102Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P102Expected]

end ConnesWeilRH.Dev
