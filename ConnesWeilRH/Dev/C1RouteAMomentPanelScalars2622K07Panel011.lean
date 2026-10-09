import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P011 : ℚ := ((-35082921974608768055528851391519566675 : ℚ) / 415140359767542390237352339322175488)

def momentPanelGrowth2622K07P011 : ℚ := ((656349676158489526634258597956439514025 : ℚ) / 191061393716517332583786000265840164864)

theorem momentPanelPhase_owner2622K07P011 :
    (momentPanelPhase2622K07P011 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P011 :
    (momentPanelGrowth2622K07P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P011Input : RatPair2542 := (momentPanelPhase2622K07P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P011Expected : RatState2542 :=
  ((((424608799607651123033446070877093217872573689208069084321449 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229796650549805 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P011_replay :
    compactExp2620 momentScalarAmp2622K07P011Input 20 = momentScalarAmp2622K07P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K07P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P011_replay] at h
  simpa only [momentPanelPhase_owner2622K07P011] using h

theorem momentScalarAmp2622K07P011_radius_le :
    (momentScalarAmp2622K07P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P011Expected]

def momentScalarGrow2622K07P011Input : RatPair2542 := (momentPanelGrowth2622K07P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P011Expected : RatState2542 :=
  ((((33150678936260953214888643317546401749367370421858553208286724232623625426259761875444629562522753 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((21011670188481351445370182721007238594839840818427 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P011_replay :
    compactExp2620 momentScalarGrow2622K07P011Input 20 = momentScalarGrow2622K07P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P011] using h

theorem momentScalarGrow2622K07P011_radius_le :
    (momentScalarGrow2622K07P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P011Expected]

end ConnesWeilRH.Dev
