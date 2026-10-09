import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P113 : ℚ := ((-19407941 : ℚ) / 629850)

def momentPanelGrowth2622K06P113 : ℚ := ((1753171 : ℚ) / 8673025)

theorem momentPanelPhase_owner2622K06P113 :
    (momentPanelPhase2622K06P113 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (47 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P113, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P113 :
    (momentPanelGrowth2622K06P113 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P113, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P113Input : RatPair2542 := (momentPanelPhase2622K06P113 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P113Expected : RatState2542 :=
  ((((44299170000521721843152252977620946350489776771241728857715717030823882497643075289 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((56157519669988052259314868225827231 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P113_replay :
    compactExp2620 momentScalarAmp2622K06P113Input 20 = momentScalarAmp2622K06P113Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P113_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (47 / 200) 0) -
      (momentScalarAmp2622K06P113Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P113]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P113 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P113 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P113Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P113_replay] at h
  simpa only [momentPanelPhase_owner2622K06P113] using h

theorem momentScalarAmp2622K06P113_radius_le :
    (momentScalarAmp2622K06P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P113Expected]

def momentScalarGrow2622K06P113Input : RatPair2542 := (momentPanelGrowth2622K06P113 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P113Expected : RatState2542 :=
  ((((2614491208428212079653103673527229534402745335259233834112935287149512457149504906674153021057787 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3314260710744287701691445736225788047190212679701 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P113_replay :
    compactExp2620 momentScalarGrow2622K06P113Input 20 = momentScalarGrow2622K06P113Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P113_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P113Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P113]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P113 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P113 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P113Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P113_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P113] using h

theorem momentScalarGrow2622K06P113_radius_le :
    (momentScalarGrow2622K06P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P113Expected]

end ConnesWeilRH.Dev
