import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P002 : ℚ := ((-10494540603049130260946986570997775 : ℚ) / 81129638414606681695789005144064)

def momentPanelGrowth2622K24P002 : ℚ := ((69824871300179185775283316532611300363 : ℚ) / 6720576422169980994974921713621401600)

theorem momentPanelPhase_owner2622K24P002 :
    (momentPanelPhase2622K24P002 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-7 / 8) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P002, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P002 :
    (momentPanelGrowth2622K24P002 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P002, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P002Input : RatPair2542 := (momentPanelPhase2622K24P002 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P002Expected : RatState2542 :=
  ((((3542330313751840487470981339151579246117 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K24P002_replay :
    compactExp2620 momentScalarAmp2622K24P002Input 20 = momentScalarAmp2622K24P002Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P002_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-7 / 8) 0) -
      (momentScalarAmp2622K24P002Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P002Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P002]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P002 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P002 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P002Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P002Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P002_replay] at h
  simpa only [momentPanelPhase_owner2622K24P002] using h

theorem momentScalarAmp2622K24P002_radius_le :
    (momentScalarAmp2622K24P002Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P002Expected]

def momentScalarGrow2622K24P002Input : RatPair2542 := (momentPanelGrowth2622K24P002 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P002Expected : RatState2542 :=
  ((((34734764380307162118478491927790388365590799984737914307511203443292896292748383747572889337397545707 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((88062217270614977439363625777646977446702016902019093 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K24P002_replay :
    compactExp2620 momentScalarGrow2622K24P002Input 20 = momentScalarGrow2622K24P002Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P002_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P002Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P002Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P002 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P002]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P002 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P002 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P002Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P002Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P002_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P002] using h

theorem momentScalarGrow2622K24P002_radius_le :
    (momentScalarGrow2622K24P002Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P002Expected]

end ConnesWeilRH.Dev
