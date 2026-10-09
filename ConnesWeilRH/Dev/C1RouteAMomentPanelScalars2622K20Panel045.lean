import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P045 : ℚ := ((-826244087375822364568348769829363273813 : ℚ) / 21687980589184731184326795800136908800)

def momentPanelGrowth2622K20P045 : ℚ := ((45408334038767230382932152282904874809 : ℚ) / 103197914183859881700564811905813708800)

theorem momentPanelPhase_owner2622K20P045 :
    (momentPanelPhase2622K20P045 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P045 :
    (momentPanelGrowth2622K20P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P045Input : RatPair2542 := (momentPanelPhase2622K20P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P045Expected : RatState2542 :=
  ((((7607640867714453853360258843913453983892432381936099975289133346611955908952267 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((38576724802199803407796753122289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K20P045_replay :
    compactExp2620 momentScalarAmp2622K20P045Input 20 = momentScalarAmp2622K20P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K20P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P045_replay] at h
  simpa only [momentPanelPhase_owner2622K20P045] using h

theorem momentScalarAmp2622K20P045_radius_le :
    (momentScalarAmp2622K20P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P045Expected]

def momentScalarGrow2622K20P045Input : RatPair2542 := (momentPanelGrowth2622K20P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P045Expected : RatState2542 :=
  ((((829150679924611588726219283244418397816922300801478631314162164372106576673458657712065864321501 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4204291664104317049934974833430979797384655270933 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P045_replay :
    compactExp2620 momentScalarGrow2622K20P045Input 20 = momentScalarGrow2622K20P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P045] using h

theorem momentScalarGrow2622K20P045_radius_le :
    (momentScalarGrow2622K20P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P045Expected]

end ConnesWeilRH.Dev
