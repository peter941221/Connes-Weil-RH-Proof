import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P026 : ℚ := ((-21010539 : ℚ) / 397850)

def momentPanelGrowth2622K06P026 : ℚ := ((1295387 : ℚ) / 1134675)

theorem momentPanelPhase_owner2622K06P026 :
    (momentPanelPhase2622K06P026 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-127 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P026 :
    (momentPanelGrowth2622K06P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P026Input : RatPair2542 := (momentPanelPhase2622K06P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P026Expected : RatState2542 :=
  ((((3099767796612132765411322207907306883472639403315181074286880883517244037 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((16927407472885012911001303 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P026_replay :
    compactExp2620 momentScalarAmp2622K06P026Input 20 = momentScalarAmp2622K06P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K06P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P026_replay] at h
  simpa only [momentPanelPhase_owner2622K06P026] using h

theorem momentScalarAmp2622K06P026_radius_le :
    (momentScalarAmp2622K06P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P026Expected]

def momentScalarGrow2622K06P026Input : RatPair2542 := (momentPanelGrowth2622K06P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P026Expected : RatState2542 :=
  ((((1672419739059734855366383666121639598477386218111130459436311789000135566913088005748611863350363 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((8480166311425055808813175611521643893926900383609 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P026_replay :
    compactExp2620 momentScalarGrow2622K06P026Input 20 = momentScalarGrow2622K06P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P026] using h

theorem momentScalarGrow2622K06P026_radius_le :
    (momentScalarGrow2622K06P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P026Expected]

end ConnesWeilRH.Dev
