import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P037 : ℚ := ((-19853398542056238195500962068538076091 : ℚ) / 470146254612645720427097284809850880)

def momentPanelGrowth2622K20P037 : ℚ := ((11020410726052090495093072437846792244163 : ℚ) / 17480219274064120567929771377129265561600)

theorem momentPanelPhase_owner2622K20P037 :
    (momentPanelPhase2622K20P037 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P037 :
    (momentPanelGrowth2622K20P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P037Input : RatPair2542 := (momentPanelPhase2622K20P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P037Expected : RatState2542 :=
  ((((488791335617864943438833457387777910036391854436624148847181626335471992439867 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((619642792540800044436166732857 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K20P037_replay :
    compactExp2620 momentScalarAmp2622K20P037Input 20 = momentScalarAmp2622K20P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K20P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P037_replay] at h
  simpa only [momentPanelPhase_owner2622K20P037] using h

theorem momentScalarAmp2622K20P037_radius_le :
    (momentScalarAmp2622K20P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P037Expected]

def momentScalarGrow2622K20P037Input : RatPair2542 := (momentPanelGrowth2622K20P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P037Expected : RatState2542 :=
  ((((1003089624691010680317245627522123543436933042371972555600188458463178053206917307742885871185983 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5086265601199820822809365573681962042613178480149 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P037_replay :
    compactExp2620 momentScalarGrow2622K20P037Input 20 = momentScalarGrow2622K20P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P037] using h

theorem momentScalarGrow2622K20P037_radius_le :
    (momentScalarGrow2622K20P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P037Expected]

end ConnesWeilRH.Dev
