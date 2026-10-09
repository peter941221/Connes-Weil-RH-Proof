import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P012 : ℚ := ((-228798342304956948722097596025926892586658300190619 : ℚ) / 3040037585463694546654149114927424640495250309120)

def momentPanelGrowth2622K01P012 : ℚ := ((104431167532445803019384646898011964132719347753010393 : ℚ) / 34198317646119822359034616571128589200245401426329600)

theorem momentPanelPhase_owner2622K01P012 :
    (momentPanelPhase2622K01P012 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P012, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P012 :
    (momentPanelGrowth2622K01P012 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P012, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P012Input : RatPair2542 := (momentPanelPhase2622K01P012 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P012Expected : RatState2542 :=
  ((((4404183252836229211031087860889756272064608776279929585768870275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851644812624845442269 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P012_replay :
    compactExp2620 momentScalarAmp2622K01P012Input 20 = momentScalarAmp2622K01P012Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P012_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 40) 0) -
      (momentScalarAmp2622K01P012Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P012]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P012 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P012 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P012Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P012_replay] at h
  simpa only [momentPanelPhase_owner2622K01P012] using h

theorem momentScalarAmp2622K01P012_radius_le :
    (momentScalarAmp2622K01P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P012Expected]

def momentScalarGrow2622K01P012Input : RatPair2542 := (momentPanelGrowth2622K01P012 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P012Expected : RatState2542 :=
  ((((45268977668543804950777030403329994620834512350560384554295188355944141673387823151037486534289645 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((28692539797264248367956951009949775874960634832487 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P012_replay :
    compactExp2620 momentScalarGrow2622K01P012Input 20 = momentScalarGrow2622K01P012Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P012_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P012Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P012]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P012 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P012 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P012Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P012_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P012] using h

theorem momentScalarGrow2622K01P012_radius_le :
    (momentScalarGrow2622K01P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P012Expected]

end ConnesWeilRH.Dev
