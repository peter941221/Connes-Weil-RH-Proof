import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K15
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K15P123 : ℚ := ((-798839731805250237442618599129603518849 : ℚ) / 24008288247842482280826361347257139200)

def momentPanelGrowth2622K15P123 : ℚ := ((456595378410706050102772558752121343083 : ℚ) / 1652516421300881125875750680066103705600)

theorem momentPanelPhase_owner2622K15P123 :
    (momentPanelPhase2622K15P123 : ℝ) = momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (67 / 200) 0 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K15P123 :
    (momentPanelGrowth2622K15P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K15P123Input : RatPair2542 := (momentPanelPhase2622K15P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K15P123Expected : RatState2542 :=
  ((((1892526770722311346071711938412896401679598028068888469184715622006457771410912837 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((9596555303668182412828067194282069 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K15P123_replay :
    compactExp2620 momentScalarAmp2622K15P123Input 20 = momentScalarAmp2622K15P123Expected := by
  decide +kernel

theorem momentScalarAmp2622K15P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622K15P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K15P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K15P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P123]
  have h := compactExp_real_error2620 momentPanelPhase2622K15P123 20 hsmall
  change |Real.exp (momentPanelPhase2622K15P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K15P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K15P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K15P123_replay] at h
  simpa only [momentPanelPhase_owner2622K15P123] using h

theorem momentScalarAmp2622K15P123_radius_le :
    (momentScalarAmp2622K15P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarAmp2622K15P123Expected]

def momentScalarGrow2622K15P123Input : RatPair2542 := (momentPanelGrowth2622K15P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K15P123Expected : RatState2542 :=
  ((((2815759226351422341306903853197765685683787719132326012284051643932099754746403901242604735829311 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((446174741604353284495650252892732060108374505159 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K15P123_replay :
    compactExp2620 momentScalarGrow2622K15P123Input 20 = momentScalarGrow2622K15P123Expected := by
  decide +kernel

theorem momentScalarGrow2622K15P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K15P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K15P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K15P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622K15P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622K15P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K15P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K15P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K15P123_replay] at h
  simpa only [momentPanelGrowth_owner2622K15P123] using h

theorem momentScalarGrow2622K15P123_radius_le :
    (momentScalarGrow2622K15P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarGrow2622K15P123Expected]

end ConnesWeilRH.Dev
