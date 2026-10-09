import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P133 : ℚ := ((-2389572751159567481582338701993422462607 : ℚ) / 65777882585602732351903330645678489600)

def momentPanelGrowth2622K20P133 : ℚ := ((565473578735688096690067508033383187 : ℚ) / 1341681395281557998544110672569958400)

theorem momentPanelPhase_owner2622K20P133 :
    (momentPanelPhase2622K20P133 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (87 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P133, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P133 :
    (momentPanelGrowth2622K20P133 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P133, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P133Input : RatPair2542 := (momentPanelPhase2622K20P133 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P133Expected : RatState2542 :=
  ((((356935212172274483102121237571342318083197526967907928097471192434978377526212747 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((452484814431382986734045808940715 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P133_replay :
    compactExp2620 momentScalarAmp2622K20P133Input 20 = momentScalarAmp2622K20P133Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P133_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (87 / 200) 0) -
      (momentScalarAmp2622K20P133Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P133]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P133 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P133 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P133Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P133_replay] at h
  simpa only [momentPanelPhase_owner2622K20P133] using h

theorem momentScalarAmp2622K20P133_radius_le :
    (momentScalarAmp2622K20P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P133Expected]

def momentScalarGrow2622K20P133Input : RatPair2542 := (momentPanelGrowth2622K20P133 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P133Expected : RatState2542 :=
  ((((3255660635629621980633427084897664175376963068379318378227385144774808111873883120430164831291269 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4127038500066327363712766932907920429670747605321 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P133_replay :
    compactExp2620 momentScalarGrow2622K20P133Input 20 = momentScalarGrow2622K20P133Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P133_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P133Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P133]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P133 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P133 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P133Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P133_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P133] using h

theorem momentScalarGrow2622K20P133_radius_le :
    (momentScalarGrow2622K20P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P133Expected]

end ConnesWeilRH.Dev
