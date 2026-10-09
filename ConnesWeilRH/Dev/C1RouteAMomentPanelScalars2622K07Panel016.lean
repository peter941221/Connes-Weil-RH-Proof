import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P016 : ℚ := ((-106209564773438013606225189667195922775 : ℚ) / 1492055180083031483067255593604481024)

def momentPanelGrowth2622K07P016 : ℚ := ((38918892777456711574274800848380401025 : ℚ) / 17296311567344449594111193268181008384)

theorem momentPanelPhase_owner2622K07P016 :
    (momentPanelPhase2622K07P016 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-147 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P016 :
    (momentPanelGrowth2622K07P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P016Input : RatPair2542 := (momentPanelPhase2622K07P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P016Expected : RatState2542 :=
  ((((260039669516757086786830893717711658795801811625794354585069538503 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231496111385221750273 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P016_replay :
    compactExp2620 momentScalarAmp2622K07P016Input 20 = momentScalarAmp2622K07P016Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622K07P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P016]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P016 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P016_replay] at h
  simpa only [momentPanelPhase_owner2622K07P016] using h

theorem momentScalarAmp2622K07P016_radius_le :
    (momentScalarAmp2622K07P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P016Expected]

def momentScalarGrow2622K07P016Input : RatPair2542 := (momentPanelGrowth2622K07P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P016Expected : RatState2542 :=
  ((((20268248932345090584264914230669874449430778210511658804931705444385767462532717894881910532052419 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((25693002790295369203780478383286876284534740284049 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P016_replay :
    compactExp2620 momentScalarGrow2622K07P016Input 20 = momentScalarGrow2622K07P016Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P016_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P016] using h

theorem momentScalarGrow2622K07P016_radius_le :
    (momentScalarGrow2622K07P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P016Expected]

end ConnesWeilRH.Dev
