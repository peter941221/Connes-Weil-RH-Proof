import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P039 : ℚ := ((-28611609893221477590984976132240343067652424447510609 : ℚ) / 708842566582414974927597726727091759484491110809600)

def momentPanelGrowth2622K01P039 : ℚ := ((1095481823662423422337229647740081960704098799372955873 : ℚ) / 1953374045349350189661798952824811764744896921573785600)

theorem momentPanelPhase_owner2622K01P039 :
    (momentPanelPhase2622K01P039 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P039 :
    (momentPanelGrowth2622K01P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P039Input : RatPair2542 := (momentPanelPhase2622K01P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P039Expected : RatState2542 :=
  ((((3153366440426752766398239267285839826438562522044375991886098382600611578985169 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3997521947314634373097412900877 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P039_replay :
    compactExp2620 momentScalarAmp2622K01P039Input 20 = momentScalarAmp2622K01P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K01P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P039_replay] at h
  simpa only [momentPanelPhase_owner2622K01P039] using h

theorem momentScalarAmp2622K01P039_radius_le :
    (momentScalarAmp2622K01P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P039Expected]

def momentScalarGrow2622K01P039Input : RatPair2542 := (momentPanelGrowth2622K01P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P039Expected : RatState2542 :=
  ((((3742463315932897469741998564952340315484677715546274010710270215494303003634988576926562955027601 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4744133331445064126668947260451575973194472068235 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P039_replay :
    compactExp2620 momentScalarGrow2622K01P039Input 20 = momentScalarGrow2622K01P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P039] using h

theorem momentScalarGrow2622K01P039_radius_le :
    (momentScalarGrow2622K01P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P039Expected]

end ConnesWeilRH.Dev
