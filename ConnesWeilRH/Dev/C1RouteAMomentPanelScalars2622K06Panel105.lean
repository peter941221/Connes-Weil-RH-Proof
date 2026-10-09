import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P105 : ℚ := ((-19596597 : ℚ) / 650650)

def momentPanelGrowth2622K06P105 : ℚ := ((436127 : ℚ) / 3090675)

theorem momentPanelPhase_owner2622K06P105 :
    (momentPanelPhase2622K06P105 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P105 :
    (momentPanelGrowth2622K06P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P105Input : RatPair2542 := (momentPanelPhase2622K06P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P105Expected : RatState2542 :=
  ((((177543024254689202493489237678360598970370196194593381261827658380207035795223227869 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((112534492940592196074345571137235427 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P105_replay :
    compactExp2620 momentScalarAmp2622K06P105Input 20 = momentScalarAmp2622K06P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K06P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P105_replay] at h
  simpa only [momentPanelPhase_owner2622K06P105] using h

theorem momentScalarAmp2622K06P105_radius_le :
    (momentScalarAmp2622K06P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P105Expected]

def momentScalarGrow2622K06P105Input : RatPair2542 := (momentPanelGrowth2622K06P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P105Expected : RatState2542 :=
  ((((307462518227428793000634190487020715460142624067652794264083485664205643285279587541082047839261 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3118039946623719374066048213771104624354049726921 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P105_replay :
    compactExp2620 momentScalarGrow2622K06P105Input 20 = momentScalarGrow2622K06P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P105] using h

theorem momentScalarGrow2622K06P105_radius_le :
    (momentScalarGrow2622K06P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P105Expected]

end ConnesWeilRH.Dev
