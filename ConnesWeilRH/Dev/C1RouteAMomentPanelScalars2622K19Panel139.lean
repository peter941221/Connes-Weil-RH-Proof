import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P139 : ℚ := ((-2386930821729668679646104456269445935331 : ℚ) / 61250848762067679513278304158639718400)

def momentPanelGrowth2622K19P139 : ℚ := ((1669712862283337207009777493977387 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K19P139 :
    (momentPanelPhase2622K19P139 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P139 :
    (momentPanelGrowth2622K19P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P139Input : RatPair2542 := (momentPanelPhase2622K19P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P139Expected : RatState2542 :=
  ((((12712099189191091968223454747194729659535909434877936787530926940541366685332299 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((32230200548128636777420428848109 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K19P139_replay :
    compactExp2620 momentScalarAmp2622K19P139Input 20 = momentScalarAmp2622K19P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K19P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P139_replay] at h
  simpa only [momentPanelPhase_owner2622K19P139] using h

theorem momentScalarAmp2622K19P139_radius_le :
    (momentScalarAmp2622K19P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P139Expected]

def momentScalarGrow2622K19P139Input : RatPair2542 := (momentPanelGrowth2622K19P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P139Expected : RatState2542 :=
  ((((3697844880002555292408840920053074995782381595952380034368606535913561506739888926930181938033431 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4687572828224817715415424978055226954461070800823 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K19P139_replay :
    compactExp2620 momentScalarGrow2622K19P139Input 20 = momentScalarGrow2622K19P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P139] using h

theorem momentScalarGrow2622K19P139_radius_le :
    (momentScalarGrow2622K19P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P139Expected]

end ConnesWeilRH.Dev
