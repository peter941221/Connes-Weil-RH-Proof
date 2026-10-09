import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P146 : ℚ := ((-795186008303776318249194645425750651331 : ℚ) / 18410343197234621243816919992316723200)

def momentPanelGrowth2622K14P146 : ℚ := ((35398768905865419104461665762618547909369 : ℚ) / 46219556018921906744674517427935825100800)

theorem momentPanelPhase_owner2622K14P146 :
    (momentPanelPhase2622K14P146 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P146 :
    (momentPanelGrowth2622K14P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P146Input : RatPair2542 := (momentPanelPhase2622K14P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P146Expected : RatState2542 :=
  ((((372733857871545051665052943907892573857219746604537008199802781112569077812819 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((472518179709774101756509016125 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K14P146_replay :
    compactExp2620 momentScalarAmp2622K14P146Input 20 = momentScalarAmp2622K14P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K14P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P146_replay] at h
  simpa only [momentPanelPhase_owner2622K14P146] using h

theorem momentScalarAmp2622K14P146_radius_le :
    (momentScalarAmp2622K14P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P146Expected]

def momentScalarGrow2622K14P146Input : RatPair2542 := (momentPanelGrowth2622K14P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P146Expected : RatState2542 :=
  ((((4594278752761460456389064567057556105422962456628932557862568366579783501544758303273757216379211 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5823935964732722944144764445606581902169076840445 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K14P146_replay :
    compactExp2620 momentScalarGrow2622K14P146Input 20 = momentScalarGrow2622K14P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P146] using h

theorem momentScalarGrow2622K14P146_radius_le :
    (momentScalarGrow2622K14P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P146Expected]

end ConnesWeilRH.Dev
