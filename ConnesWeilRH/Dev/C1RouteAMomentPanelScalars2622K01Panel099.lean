import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P099 : ℚ := ((-28528273981498869063808440523937822806006272232612169 : ℚ) / 942911188186192395421156625716808961851261557145600)

def momentPanelGrowth2622K01P099 : ℚ := ((7353301976938099033991354770170852993836094383891 : ℚ) / 116570455301759273285435506554787515264060830515200)

theorem momentPanelPhase_owner2622K01P099 :
    (momentPanelPhase2622K01P099 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P099, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P099 :
    (momentPanelGrowth2622K01P099 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P099, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P099Input : RatPair2542 := (momentPanelPhase2622K01P099 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P099Expected : RatState2542 :=
  ((((302357438367959409221028732738911109705494250619722242130699104158210604894477241 : ℚ) / 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048), 0), ((98123429792805802266615849790008977 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P099_replay :
    compactExp2620 momentScalarAmp2622K01P099Input 20 = momentScalarAmp2622K01P099Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P099_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 200) 0) -
      (momentScalarAmp2622K01P099Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P099]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P099 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P099 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P099Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P099_replay] at h
  simpa only [momentPanelPhase_owner2622K01P099] using h

theorem momentScalarAmp2622K01P099_radius_le :
    (momentScalarAmp2622K01P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P099Expected]

def momentScalarGrow2622K01P099Input : RatPair2542 := (momentPanelGrowth2622K01P099 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P099Expected : RatState2542 :=
  ((((568766563599146019331283869773413685280480129230837495686284586546283228667010711782038780446139 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2883988929449566158625232929879248303833740323955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P099_replay :
    compactExp2620 momentScalarGrow2622K01P099Input 20 = momentScalarGrow2622K01P099Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P099_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P099Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P099]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P099 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P099 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P099Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P099_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P099] using h

theorem momentScalarGrow2622K01P099_radius_le :
    (momentScalarGrow2622K01P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P099Expected]

end ConnesWeilRH.Dev
