import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P076 : ℚ := ((-100828148003734306741731136778073725775 : ℚ) / 3186042030180018996875330021012537344)

def momentPanelGrowth2622K07P076 : ℚ := ((13657005375067534716435052280251087025 : ℚ) / 81229711823591099037660760881909202944)

theorem momentPanelPhase_owner2622K07P076 :
    (momentPanelPhase2622K07P076 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P076 :
    (momentPanelGrowth2622K07P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P076Input : RatPair2542 := (momentPanelPhase2622K07P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P076Expected : RatState2542 :=
  ((((38508144077348055586248355011460825574314979469253929480632609255902102876844015691 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((762755394509437382409839078015005 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K07P076_replay :
    compactExp2620 momentScalarAmp2622K07P076Input 20 = momentScalarAmp2622K07P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K07P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P076_replay] at h
  simpa only [momentPanelPhase_owner2622K07P076] using h

theorem momentScalarAmp2622K07P076_radius_le :
    (momentScalarAmp2622K07P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P076Expected]

def momentScalarGrow2622K07P076Input : RatPair2542 := (momentPanelGrowth2622K07P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P076Expected : RatState2542 :=
  ((((631765304371600029434964936590885264152315535511243611708735224454648625421669710492953047460173 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3203430155523531468411111813400202674586213691371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P076_replay :
    compactExp2620 momentScalarGrow2622K07P076Input 20 = momentScalarGrow2622K07P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P076] using h

theorem momentScalarGrow2622K07P076_radius_le :
    (momentScalarGrow2622K07P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P076Expected]

end ConnesWeilRH.Dev
