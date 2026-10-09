import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P080 : ℚ := ((-28561633726739526178522998254041982649303592727387831 : ℚ) / 942911188186192395421156625716808961851261557145600)

def momentPanelGrowth2622K01P080 : ℚ := ((7353301976938099033991354770170852993836094383891 : ℚ) / 116570455301759273285435506554787515264060830515200)

theorem momentPanelPhase_owner2622K01P080 :
    (momentPanelPhase2622K01P080 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P080 :
    (momentPanelGrowth2622K01P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P080Input : RatPair2542 := (momentPanelPhase2622K01P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P080Expected : RatState2542 :=
  ((((18678220624942817543050333229823891196385298983504701451971461811061784580850118707 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((94712566331590696312794353177852359 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P080_replay :
    compactExp2620 momentScalarAmp2622K01P080Input 20 = momentScalarAmp2622K01P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K01P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P080_replay] at h
  simpa only [momentPanelPhase_owner2622K01P080] using h

theorem momentScalarAmp2622K01P080_radius_le :
    (momentScalarAmp2622K01P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P080Expected]

def momentScalarGrow2622K01P080Input : RatPair2542 := (momentPanelGrowth2622K01P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P080Expected : RatState2542 :=
  ((((568766563599146019331283869773413685280480129230837495686284586546283228667010711782038780446139 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2883988929449566158625232929879248303833740323955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P080_replay :
    compactExp2620 momentScalarGrow2622K01P080Input 20 = momentScalarGrow2622K01P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P080] using h

theorem momentScalarGrow2622K01P080_radius_le :
    (momentScalarGrow2622K01P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P080Expected]

end ConnesWeilRH.Dev
