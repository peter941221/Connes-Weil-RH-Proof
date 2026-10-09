import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K27
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K27P039 : ℚ := ((-827053861897759195039826812994480237977 : ℚ) / 20146517459307204232106804702399692800)

def momentPanelGrowth2622K27P039 : ℚ := ((31891953032482833028955654157281809344169 : ℚ) / 55518229525812051567237374252522720460800)

theorem momentPanelPhase_owner2622K27P039 :
    (momentPanelPhase2622K27P039 : ℝ) = momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K27P039 :
    (momentPanelGrowth2622K27P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K27P039Input : RatPair2542 := (momentPanelPhase2622K27P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K27P039Expected : RatState2542 :=
  ((((3169293885358815256800456368689548964186271615053457555179615064813565320903971 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4017717005144830374403709565567 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K27P039_replay :
    compactExp2620 momentScalarAmp2622K27P039Input 20 = momentScalarAmp2622K27P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K27P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K27P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K27P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K27P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K27P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K27P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K27P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K27P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K27P039_replay] at h
  simpa only [momentPanelPhase_owner2622K27P039] using h

theorem momentScalarAmp2622K27P039_radius_le :
    (momentScalarAmp2622K27P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarAmp2622K27P039Expected]

def momentScalarGrow2622K27P039Input : RatPair2542 := (momentPanelGrowth2622K27P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K27P039Expected : RatState2542 :=
  ((((1896903414292533571972076527923901225636847756864107560275363604694788444660839619984681770410969 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4809218868772035759096176413003708967556826428309 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K27P039_replay :
    compactExp2620 momentScalarGrow2622K27P039Input 20 = momentScalarGrow2622K27P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K27P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K27P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K27P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K27P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K27P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K27P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K27P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K27P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K27P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K27P039] using h

theorem momentScalarGrow2622K27P039_radius_le :
    (momentScalarGrow2622K27P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarGrow2622K27P039Expected]

end ConnesWeilRH.Dev
