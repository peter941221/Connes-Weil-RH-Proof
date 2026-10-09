import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P052 : ℚ := ((-31626053002348074276555147734976513 : ℚ) / 892426022560673498653679056584704)

def momentPanelGrowth2622K05P052 : ℚ := ((503533443422339668183978542456200821523 : ℚ) / 1546642243169819406262746028353100185600)

theorem momentPanelPhase_owner2622K05P052 :
    (momentPanelPhase2622K05P052 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P052, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P052 :
    (momentPanelGrowth2622K05P052 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P052, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P052Input : RatPair2542 := (momentPanelPhase2622K05P052 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P052Expected : RatState2542 :=
  ((((868849234011545593952840995913063607515144808445759903671834639526212790580945415 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1101434479518472010862729441005099 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P052_replay :
    compactExp2620 momentScalarAmp2622K05P052Input 20 = momentScalarAmp2622K05P052Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P052_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 8) 0) -
      (momentScalarAmp2622K05P052Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P052]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P052 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P052 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P052Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P052_replay] at h
  simpa only [momentPanelPhase_owner2622K05P052] using h

theorem momentScalarAmp2622K05P052_radius_le :
    (momentScalarAmp2622K05P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P052Expected]

def momentScalarGrow2622K05P052Input : RatPair2542 := (momentPanelGrowth2622K05P052 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P052Expected : RatState2542 :=
  ((((1478971965073249942101029892496584933381052538554765778249599656069909276917479643508307927252179 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3749638234290637394472849210440019794709510063013 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P052_replay :
    compactExp2620 momentScalarGrow2622K05P052Input 20 = momentScalarGrow2622K05P052Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P052_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P052Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P052]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P052 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P052 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P052Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P052_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P052] using h

theorem momentScalarGrow2622K05P052_radius_le :
    (momentScalarGrow2622K05P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P052Expected]

end ConnesWeilRH.Dev
