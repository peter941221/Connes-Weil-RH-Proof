import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K28
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K28P110 : ℚ := ((-803070896351888359356451792862208812283 : ℚ) / 25906721786744278632507824067628236800)

def momentPanelGrowth2622K28P110 : ℚ := ((14213109428006367386023293585777012748489 : ℚ) / 92664732548154354488561502881814727884800)

theorem momentPanelPhase_owner2622K28P110 :
    (momentPanelPhase2622K28P110 : ℝ) = momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (41 / 200) 0 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P110, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K28P110 :
    (momentPanelGrowth2622K28P110 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2))
      (41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P110, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K28P110Input : RatPair2542 := (momentPanelPhase2622K28P110 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K28P110Expected : RatState2542 :=
  ((((73637318221057001842188856310100107709926454791531096239594273906285668635418360547 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((93349150240254364991500220645626679 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K28P110_replay :
    compactExp2620 momentScalarAmp2622K28P110Input 20 = momentScalarAmp2622K28P110Expected := by
  decide +kernel

theorem momentScalarAmp2622K28P110_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (41 / 200) 0) -
      (momentScalarAmp2622K28P110Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K28P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K28P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelPhase2622K28P110]
  have h := compactExp_real_error2620 momentPanelPhase2622K28P110 20 hsmall
  change |Real.exp (momentPanelPhase2622K28P110 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K28P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K28P110Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K28P110_replay] at h
  simpa only [momentPanelPhase_owner2622K28P110] using h

theorem momentScalarAmp2622K28P110_radius_le :
    (momentScalarAmp2622K28P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarAmp2622K28P110Expected]

def momentScalarGrow2622K28P110Input : RatPair2542 := (momentPanelGrowth2622K28P110 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K28P110Expected : RatState2542 :=
  ((((2490070272164054361941704982727624362214744831991655878025472574535998609243839869507333387003347 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3156538613391620882402703960499552724493190246867 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K28P110_replay :
    compactExp2620 momentScalarGrow2622K28P110Input 20 = momentScalarGrow2622K28P110Expected := by
  decide +kernel

theorem momentScalarGrow2622K28P110_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 28).re * (storedWidth 28 ^ 2)) (41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K28P110Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K28P110Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K28P110 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentPanelGrowth2622K28P110]
  have h := compactExp_real_error2620 momentPanelGrowth2622K28P110 20 hsmall
  change |Real.exp (momentPanelGrowth2622K28P110 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K28P110Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K28P110Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K28P110_replay] at h
  simpa only [momentPanelGrowth_owner2622K28P110] using h

theorem momentScalarGrow2622K28P110_radius_le :
    (momentScalarGrow2622K28P110Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, momentScalarGrow2622K28P110Expected]

end ConnesWeilRH.Dev
