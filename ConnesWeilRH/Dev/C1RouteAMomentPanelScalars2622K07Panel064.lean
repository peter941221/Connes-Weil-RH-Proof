import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P064 : ℚ := ((-103602212738316252646479381992647445175 : ℚ) / 3034167347067875288740813003382849536)

def momentPanelGrowth2622K07P064 : ℚ := ((19115278367102369171450709422773861025 : ℚ) / 73470473205618116000275500429930921984)

theorem momentPanelPhase_owner2622K07P064 :
    (momentPanelPhase2622K07P064 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P064 :
    (momentPanelGrowth2622K07P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P064Input : RatPair2542 := (momentPanelPhase2622K07P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P064Expected : RatState2542 :=
  ((((1583077350794702928352643346635694288444431206299599046515886269560670876184987685 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4013708608126846332859667726362963 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P064_replay :
    compactExp2620 momentScalarAmp2622K07P064Input 20 = momentScalarAmp2622K07P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K07P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P064_replay] at h
  simpa only [momentPanelPhase_owner2622K07P064] using h

theorem momentScalarAmp2622K07P064_radius_le :
    (momentScalarAmp2622K07P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P064Expected]

def momentScalarGrow2622K07P064Input : RatPair2542 := (momentPanelGrowth2622K07P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P064Expected : RatState2542 :=
  ((((2770714379358845694287669678749645536982860015241339047620249236595752751023900750250481371005609 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3512296874571769634896887691989707310221366799451 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P064_replay :
    compactExp2620 momentScalarGrow2622K07P064Input 20 = momentScalarGrow2622K07P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P064] using h

theorem momentScalarGrow2622K07P064_radius_le :
    (momentScalarGrow2622K07P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P064Expected]

end ConnesWeilRH.Dev
