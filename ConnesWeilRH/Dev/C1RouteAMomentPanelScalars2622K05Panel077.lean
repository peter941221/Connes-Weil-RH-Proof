import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P077 : ℚ := ((-52223505217891345334178162230163829 : ℚ) / 1703722406706740315611569108025344)

def momentPanelGrowth2622K05P077 : ℚ := ((3097767741539374204275576775449374607643 : ℚ) / 32671095030091904862012696278314097049600)

theorem momentPanelPhase_owner2622K05P077 :
    (momentPanelPhase2622K05P077 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P077 :
    (momentPanelGrowth2622K05P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P077Input : RatPair2542 := (momentPanelPhase2622K05P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P077Expected : RatState2542 :=
  ((((104075309872667260332139909866173628893661838757891962607506869374222588045363519367 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((131934985776189216778282354153903237 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P077_replay :
    compactExp2620 momentScalarAmp2622K05P077Input 20 = momentScalarAmp2622K05P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K05P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P077_replay] at h
  simpa only [momentPanelPhase_owner2622K05P077] using h

theorem momentScalarAmp2622K05P077_radius_le :
    (momentScalarAmp2622K05P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P077Expected]

def momentScalarGrow2622K05P077Input : RatPair2542 := (momentPanelGrowth2622K05P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P077Expected : RatState2542 :=
  ((((2348426719594993480262601959507901673230110657760928429382922567905247747672064580919257659200883 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((372123033936852054099951466642402141427375892451 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K05P077_replay :
    compactExp2620 momentScalarGrow2622K05P077Input 20 = momentScalarGrow2622K05P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P077] using h

theorem momentScalarGrow2622K05P077_radius_le :
    (momentScalarGrow2622K05P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P077Expected]

end ConnesWeilRH.Dev
