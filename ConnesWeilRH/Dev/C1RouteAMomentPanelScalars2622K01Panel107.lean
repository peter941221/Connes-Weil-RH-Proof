import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P107 : ℚ := ((-228119180004969302929452774305044504192881019248013 : ℚ) / 7378870571289812585071338462053889855098800046080)

def momentPanelGrowth2622K01P107 : ℚ := ((24473589751536728696444422499659630691757203794752153 : ℚ) / 208790673399454482689132622641946430243674030447001600)

theorem momentPanelPhase_owner2622K01P107 :
    (momentPanelPhase2622K01P107 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P107 :
    (momentPanelGrowth2622K01P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P107Input : RatPair2542 := (momentPanelPhase2622K01P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P107Expected : RatState2542 :=
  ((((20009790062635994202184677302478043386983886061062019988821528922563266046381422331 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((101464680977101535435062779442642245 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P107_replay :
    compactExp2620 momentScalarAmp2622K01P107Input 20 = momentScalarAmp2622K01P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K01P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P107_replay] at h
  simpa only [momentPanelPhase_owner2622K01P107] using h

theorem momentScalarAmp2622K01P107_radius_le :
    (momentScalarAmp2622K01P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P107Expected]

def momentScalarGrow2622K01P107Input : RatPair2542 := (momentPanelGrowth2622K01P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P107Expected : RatState2542 :=
  ((((2401623018246691756820186808613600030367141388659471699016488679993739844370514987481259835400957 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3044418520279549817292458938357667234392511813105 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P107_replay :
    compactExp2620 momentScalarGrow2622K01P107Input 20 = momentScalarGrow2622K01P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P107] using h

theorem momentScalarGrow2622K01P107_radius_le :
    (momentScalarGrow2622K01P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P107Expected]

end ConnesWeilRH.Dev
