import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P153 : ℚ := ((-795424153258807861107611708240350376109 : ℚ) / 16138713321625634156334827848282931200)

def momentPanelGrowth2622K16P153 : ℚ := ((51418903911122094917207214744933002803 : ℚ) / 46027886234046918276584694705920409600)

theorem momentPanelPhase_owner2622K16P153 :
    (momentPanelPhase2622K16P153 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (127 / 200) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P153, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P153 :
    (momentPanelGrowth2622K16P153 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P153, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P153Input : RatPair2542 := (momentPanelPhase2622K16P153 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P153Expected : RatState2542 :=
  ((((840718384549211082667882134175386699188415989406399315335533934750006498399 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((534102555481016633731496477 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K16P153_replay :
    compactExp2620 momentScalarAmp2622K16P153Input 20 = momentScalarAmp2622K16P153Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P153_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (127 / 200) 0) -
      (momentScalarAmp2622K16P153Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P153]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P153 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P153 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P153Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P153_replay] at h
  simpa only [momentPanelPhase_owner2622K16P153] using h

theorem momentScalarAmp2622K16P153_radius_le :
    (momentScalarAmp2622K16P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P153Expected]

def momentScalarGrow2622K16P153Input : RatPair2542 := (momentPanelGrowth2622K16P153 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P153Expected : RatState2542 :=
  ((((3263847466147438529496068662583120271770936461268829072955156058846325455421353747134945036245419 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8274827583244050598257714814911676980882681246901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K16P153_replay :
    compactExp2620 momentScalarGrow2622K16P153Input 20 = momentScalarGrow2622K16P153Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P153_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P153Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P153Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P153 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P153]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P153 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P153 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P153Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P153Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P153_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P153] using h

theorem momentScalarGrow2622K16P153_radius_le :
    (momentScalarGrow2622K16P153Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P153Expected]

end ConnesWeilRH.Dev
