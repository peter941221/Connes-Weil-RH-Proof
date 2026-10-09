import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P140 : ℚ := ((-28478297815016917651346462645739462387657440512489391 : ℚ) / 708842566582414974927597726727091759484491110809600)

def momentPanelGrowth2622K01P140 : ℚ := ((1095481823662423422337229647740081960704098799372955873 : ℚ) / 1953374045349350189661798952824811764744896921573785600)

theorem momentPanelPhase_owner2622K01P140 :
    (momentPanelPhase2622K01P140 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P140 :
    (momentPanelGrowth2622K01P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P140Input : RatPair2542 := (momentPanelPhase2622K01P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P140Expected : RatState2542 :=
  ((((951463752864860134843106909267758201989256791020496991073746944709240111076971 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9649360901420468757076298745859 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P140_replay :
    compactExp2620 momentScalarAmp2622K01P140Input 20 = momentScalarAmp2622K01P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K01P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P140_replay] at h
  simpa only [momentPanelPhase_owner2622K01P140] using h

theorem momentScalarAmp2622K01P140_radius_le :
    (momentScalarAmp2622K01P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P140Expected]

def momentScalarGrow2622K01P140Input : RatPair2542 := (momentPanelGrowth2622K01P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P140Expected : RatState2542 :=
  ((((3742463315932897469741998564952340315484677715546274010710270215494303003634988576926562955027601 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4744133331445064126668947260451575973194472068235 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P140_replay :
    compactExp2620 momentScalarGrow2622K01P140Input 20 = momentScalarGrow2622K01P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P140] using h

theorem momentScalarGrow2622K01P140_radius_le :
    (momentScalarGrow2622K01P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P140Expected]

end ConnesWeilRH.Dev
