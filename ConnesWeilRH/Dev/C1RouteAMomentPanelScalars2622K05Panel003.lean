import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P003 : ℚ := ((-819607810586654689524206617555413988729 : ℚ) / 6808804903945865761319092256715571200)

def momentPanelGrowth2622K05P003 : ℚ := ((53021665240296305534375560381683397269729 : ℚ) / 5993209663084304972814846585364860108800)

theorem momentPanelPhase_owner2622K05P003 :
    (momentPanelPhase2622K05P003 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-173 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P003 :
    (momentPanelGrowth2622K05P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P003Input : RatPair2542 := (momentPanelPhase2622K05P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P003Expected : RatState2542 :=
  ((((112598604247947203428250906862322703832470683 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P003_replay :
    compactExp2620 momentScalarAmp2622K05P003Input 20 = momentScalarAmp2622K05P003Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622K05P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P003]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P003 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P003_replay] at h
  simpa only [momentPanelPhase_owner2622K05P003] using h

theorem momentScalarAmp2622K05P003_radius_le :
    (momentScalarAmp2622K05P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P003Expected]

def momentScalarGrow2622K05P003Input : RatPair2542 := (momentPanelGrowth2622K05P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P003Expected : RatState2542 :=
  ((((14851933845417579555537593233264010421095216370828491215605089388926572617623252300272356308379260007 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((18826904008265451811267090612376795985560732789060655 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P003_replay :
    compactExp2620 momentScalarGrow2622K05P003Input 20 = momentScalarGrow2622K05P003Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P003_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P003] using h

theorem momentScalarGrow2622K05P003_radius_le :
    (momentScalarGrow2622K05P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P003Expected]

end ConnesWeilRH.Dev
