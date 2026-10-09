import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P067 : ℚ := ((-19666762567291141557805813743189187719 : ℚ) / 616179603758937747479517494069166080)

def momentPanelGrowth2622K05P067 : ℚ := ((5092860370011133710776870556047778622283 : ℚ) / 30322148609073797606874517212378012057600)

theorem momentPanelPhase_owner2622K05P067 :
    (momentPanelPhase2622K05P067 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P067 :
    (momentPanelGrowth2622K05P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P067Input : RatPair2542 := (momentPanelPhase2622K05P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P067Expected : RatState2542 :=
  ((((14691974572376904444947938308493403460301192745667054879664737418142173634537795627 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((37249714587277729584739654997190987 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P067_replay :
    compactExp2620 momentScalarAmp2622K05P067Input 20 = momentScalarAmp2622K05P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K05P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P067_replay] at h
  simpa only [momentPanelPhase_owner2622K05P067] using h

theorem momentScalarAmp2622K05P067_radius_le :
    (momentScalarAmp2622K05P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P067Expected]

def momentScalarGrow2622K05P067Input : RatPair2542 := (momentPanelGrowth2622K05P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P067Expected : RatState2542 :=
  ((((1263316110829721831465866586044500617360476818886492141525773398854322624721759675013887434995733 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((100090198103492814799227966663637777379766834237 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P067_replay :
    compactExp2620 momentScalarGrow2622K05P067Input 20 = momentScalarGrow2622K05P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P067] using h

theorem momentScalarGrow2622K05P067_radius_le :
    (momentScalarGrow2622K05P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P067Expected]

end ConnesWeilRH.Dev
