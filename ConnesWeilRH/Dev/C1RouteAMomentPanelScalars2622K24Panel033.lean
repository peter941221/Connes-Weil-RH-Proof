import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P033 : ℚ := ((-827406759988357315666585457455529348669 : ℚ) / 18410343197234621243816919992316723200)

def momentPanelGrowth2622K24P033 : ℚ := ((35398768905865419104461665762618547909369 : ℚ) / 46219556018921906744674517427935825100800)

theorem momentPanelPhase_owner2622K24P033 :
    (momentPanelPhase2622K24P033 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-113 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P033, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P033 :
    (momentPanelGrowth2622K24P033 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P033, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P033Input : RatPair2542 := (momentPanelPhase2622K24P033 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P033Expected : RatState2542 :=
  ((((32381052962548566031180284244927975070965426918237499038803630028548547866447 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((41050829519513650385796962421 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K24P033_replay :
    compactExp2620 momentScalarAmp2622K24P033Input 20 = momentScalarAmp2622K24P033Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P033_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-113 / 200) 0) -
      (momentScalarAmp2622K24P033Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P033]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P033 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P033 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P033Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P033_replay] at h
  simpa only [momentPanelPhase_owner2622K24P033] using h

theorem momentScalarAmp2622K24P033_radius_le :
    (momentScalarAmp2622K24P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P033Expected]

def momentScalarGrow2622K24P033Input : RatPair2542 := (momentPanelGrowth2622K24P033 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P033Expected : RatState2542 :=
  ((((4594278752761460456389064567057556105422962456628932557862568366579783501544758303273757216379211 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5823935964732722944144764445606581902169076840445 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K24P033_replay :
    compactExp2620 momentScalarGrow2622K24P033Input 20 = momentScalarGrow2622K24P033Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P033_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P033Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P033]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P033 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P033 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P033Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P033_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P033] using h

theorem momentScalarGrow2622K24P033_radius_le :
    (momentScalarGrow2622K24P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P033Expected]

end ConnesWeilRH.Dev
