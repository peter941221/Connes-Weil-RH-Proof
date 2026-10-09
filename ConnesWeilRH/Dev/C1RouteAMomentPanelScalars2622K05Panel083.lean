import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P083 : ℚ := ((-813766523351474734143821623340227102489 : ℚ) / 26928955230768322821874765532443443200)

def momentPanelGrowth2622K05P083 : ℚ := ((1892147385634496820600283834270855511563 : ℚ) / 33473548283650779550665745328194034073600)

theorem momentPanelPhase_owner2622K05P083 :
    (momentPanelPhase2622K05P083 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P083 :
    (momentPanelGrowth2622K05P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P083Input : RatPair2542 := (momentPanelPhase2622K05P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P083Expected : RatState2542 :=
  ((((40140873105075672730207531557050834061831375449976265629448098555521097584751252779 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((203544273421842993560071221019283909 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P083_replay :
    compactExp2620 momentScalarAmp2622K05P083Input 20 = momentScalarAmp2622K05P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K05P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P083_replay] at h
  simpa only [momentPanelPhase_owner2622K05P083] using h

theorem momentScalarAmp2622K05P083_radius_le :
    (momentScalarAmp2622K05P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P083Expected]

def momentScalarGrow2622K05P083Input : RatPair2542 := (momentPanelGrowth2622K05P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P083Expected : RatState2542 :=
  ((((2260204954266660985062012717051038787466760927010629127993918421342096387215813928771953358467265 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1432575006230205948484797428595388259207107349783 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P083_replay :
    compactExp2620 momentScalarGrow2622K05P083Input 20 = momentScalarGrow2622K05P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P083] using h

theorem momentScalarGrow2622K05P083_radius_le :
    (momentScalarGrow2622K05P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P083Expected]

end ConnesWeilRH.Dev
