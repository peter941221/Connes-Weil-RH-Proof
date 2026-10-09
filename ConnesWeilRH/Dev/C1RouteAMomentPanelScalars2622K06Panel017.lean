import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P017 : ℚ := ((-167337 : ℚ) / 2530)

def momentPanelGrowth2622K06P017 : ℚ := ((372272747 : ℚ) / 181818675)

theorem momentPanelPhase_owner2622K06P017 :
    (momentPanelPhase2622K06P017 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P017 :
    (momentPanelGrowth2622K06P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P017Input : RatPair2542 := (momentPanelPhase2622K06P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P017Expected : RatState2542 :=
  ((((40260664375850754091839591521251584233333402795354470798946684858975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417902678903972819293515 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P017_replay :
    compactExp2620 momentScalarAmp2622K06P017Input 20 = momentScalarAmp2622K06P017Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622K06P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P017]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P017 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P017_replay] at h
  simpa only [momentPanelPhase_owner2622K06P017] using h

theorem momentScalarAmp2622K06P017_radius_le :
    (momentScalarAmp2622K06P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P017Expected]

def momentScalarGrow2622K06P017Input : RatPair2542 := (momentPanelGrowth2622K06P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P017Expected : RatState2542 :=
  ((((16550617402680033412578827656272894582663796220017260657282224000170924359948524179643543297865637 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20980359117464392728874535093049558771825528418721 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P017_replay :
    compactExp2620 momentScalarGrow2622K06P017Input 20 = momentScalarGrow2622K06P017Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P017_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P017] using h

theorem momentScalarGrow2622K06P017_radius_le :
    (momentScalarGrow2622K06P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P017Expected]

end ConnesWeilRH.Dev
