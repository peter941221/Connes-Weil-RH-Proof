import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P088 : ℚ := ((-60119973 : ℚ) / 1999550)

def momentPanelGrowth2622K06P088 : ℚ := ((2706667 : ℚ) / 52041675)

theorem momentPanelPhase_owner2622K06P088 :
    (momentPanelPhase2622K06P088 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P088 :
    (momentPanelGrowth2622K06P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P088Input : RatPair2542 := (momentPanelPhase2622K06P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P088Expected : RatState2542 :=
  ((((93485518973678759391945163283808672375019650596052780701754224345856014556482367333 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((237020744690696481211385889186765199 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P088_replay :
    compactExp2620 momentScalarAmp2622K06P088Input 20 = momentScalarAmp2622K06P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K06P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P088_replay] at h
  simpa only [momentPanelPhase_owner2622K06P088] using h

theorem momentScalarAmp2622K06P088_radius_le :
    (momentScalarAmp2622K06P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P088Expected]

def momentScalarGrow2622K06P088Input : RatPair2542 := (momentPanelGrowth2622K06P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P088Expected : RatState2542 :=
  ((((562504635750834975249070708880879036819445101660032418089791381360508663136159871402939482416773 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2852237215091218300858698823132417326758486320461 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P088_replay :
    compactExp2620 momentScalarGrow2622K06P088Input 20 = momentScalarGrow2622K06P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P088] using h

theorem momentScalarGrow2622K06P088_radius_le :
    (momentScalarGrow2622K06P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P088Expected]

end ConnesWeilRH.Dev
