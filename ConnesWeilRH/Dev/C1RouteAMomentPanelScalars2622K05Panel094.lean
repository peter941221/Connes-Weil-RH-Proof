import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P094 : ℚ := ((-2428747528794848976575683342148545813881 : ℚ) / 80965350896817103165355032408647270400)

def momentPanelGrowth2622K05P094 : ℚ := ((2382048838728469120418353819113449963 : ℚ) / 53816331521849159719380439199750553600)

theorem momentPanelPhase_owner2622K05P094 :
    (momentPanelPhase2622K05P094 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P094 :
    (momentPanelGrowth2622K05P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P094Input : RatPair2542 := (momentPanelPhase2622K05P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P094Expected : RatState2542 :=
  ((((100202065051660747062927990564475645844257434906010062449549862794920975741703840787 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((254049683494524909485762286418363665 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P094_replay :
    compactExp2620 momentScalarAmp2622K05P094Input 20 = momentScalarAmp2622K05P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K05P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P094_replay] at h
  simpa only [momentPanelPhase_owner2622K05P094] using h

theorem momentScalarAmp2622K05P094_radius_le :
    (momentScalarAmp2622K05P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P094Expected]

def momentScalarGrow2622K05P094Input : RatPair2542 := (momentPanelGrowth2622K05P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P094Expected : RatState2542 :=
  ((((1116327450753403023628052868813664908463861295081645960627872594738768711700312745782272062120193 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2830226206527889523152128881474069951390472377155 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P094_replay :
    compactExp2620 momentScalarGrow2622K05P094Input 20 = momentScalarGrow2622K05P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P094] using h

theorem momentScalarGrow2622K05P094_radius_le :
    (momentScalarGrow2622K05P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P094Expected]

end ConnesWeilRH.Dev
