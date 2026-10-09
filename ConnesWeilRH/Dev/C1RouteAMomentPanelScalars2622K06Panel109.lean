import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P109 : ℚ := ((-58499319 : ℚ) / 1923950)

def momentPanelGrowth2622K06P109 : ℚ := ((817 : ℚ) / 4800)

theorem momentPanelPhase_owner2622K06P109 :
    (momentPanelPhase2622K06P109 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (39 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P109, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P109 :
    (momentPanelGrowth2622K06P109 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P109, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P109Input : RatPair2542 := (momentPanelPhase2622K06P109 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P109Expected : RatState2542 :=
  ((((133201579848958244275798697511612780441301785847298296630016175332334176383876027169 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((168857958998174840502195107964540459 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P109_replay :
    compactExp2620 momentScalarAmp2622K06P109Input 20 = momentScalarAmp2622K06P109Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P109_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (39 / 200) 0) -
      (momentScalarAmp2622K06P109Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P109]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P109 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P109 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P109Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P109_replay] at h
  simpa only [momentPanelPhase_owner2622K06P109] using h

theorem momentScalarAmp2622K06P109_radius_le :
    (momentScalarAmp2622K06P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P109Expected]

def momentScalarGrow2622K06P109Input : RatPair2542 := (momentPanelGrowth2622K06P109 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P109Expected : RatState2542 :=
  ((((316540413554908826619080828850161444754619873052418948326785723275317071490773568215403553702293 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3210100640840754341043570042387494844150807032035 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P109_replay :
    compactExp2620 momentScalarGrow2622K06P109Input 20 = momentScalarGrow2622K06P109Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P109_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P109Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P109]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P109 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P109 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P109Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P109_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P109] using h

theorem momentScalarGrow2622K06P109_radius_le :
    (momentScalarGrow2622K06P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P109Expected]

end ConnesWeilRH.Dev
