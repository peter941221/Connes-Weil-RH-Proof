import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P107 : ℚ := ((-6438578593493612302907305794549518909 : ℚ) / 209720115301758272183614578297405440)

def momentPanelGrowth2622K05P107 : ℚ := ((768274583078498813317434247599465889929 : ℚ) / 5934187851137678611881160084122553548800)

theorem momentPanelPhase_owner2622K05P107 :
    (momentPanelPhase2622K05P107 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P107 :
    (momentPanelGrowth2622K05P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P107Input : RatPair2542 := (momentPanelPhase2622K05P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P107Expected : RatState2542 :=
  ((((99175362151831346823055661142719817290546527739429217380815753561338719417756621897 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((125723388310353853332462616490549487 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P107_replay :
    compactExp2620 momentScalarAmp2622K05P107Input 20 = momentScalarAmp2622K05P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K05P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P107_replay] at h
  simpa only [momentPanelPhase_owner2622K05P107] using h

theorem momentScalarAmp2622K05P107_radius_le :
    (momentScalarAmp2622K05P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P107Expected]

def momentScalarGrow2622K05P107Input : RatPair2542 := (momentPanelGrowth2622K05P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P107Expected : RatState2542 :=
  ((((2431223640561839337960200450603739485955037167030366390346532585070093712069007229514606283425265 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3081941726725328310060240933117124677190349877883 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P107_replay :
    compactExp2620 momentScalarGrow2622K05P107Input 20 = momentScalarGrow2622K05P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P107] using h

theorem momentScalarGrow2622K05P107_radius_le :
    (momentScalarGrow2622K05P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P107Expected]

end ConnesWeilRH.Dev
