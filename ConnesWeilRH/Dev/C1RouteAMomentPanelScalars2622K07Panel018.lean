import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P018 : ℚ := ((-35503967826958294554417020789223580825 : ℚ) / 528721853547991744611456946523865088)

def momentPanelGrowth2622K07P018 : ℚ := ((7142035252936670580948884476322301075 : ℚ) / 3675213185000889984160089827528671232)

theorem momentPanelPhase_owner2622K07P018 :
    (momentPanelPhase2622K07P018 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-143 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P018 :
    (momentPanelGrowth2622K07P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P018Input : RatPair2542 := (momentPanelPhase2622K07P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P018Expected : RatState2542 :=
  ((((1833967159886292059698374891311749916952079555521908992068345160555 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417870239056929670782987 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P018_replay :
    compactExp2620 momentScalarAmp2622K07P018Input 20 = momentScalarAmp2622K07P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K07P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P018_replay] at h
  simpa only [momentPanelPhase_owner2622K07P018] using h

theorem momentScalarAmp2622K07P018_radius_le :
    (momentScalarAmp2622K07P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P018Expected]

def momentScalarGrow2622K07P018Input : RatPair2542 := (momentPanelGrowth2622K07P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P018Expected : RatState2542 :=
  ((((233014170835224537561627172266374585511235418698877178769269202654933006901919321437959425002713 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((4726080097607674232776086073045668135569625428733 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P018_replay :
    compactExp2620 momentScalarGrow2622K07P018Input 20 = momentScalarGrow2622K07P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P018] using h

theorem momentScalarGrow2622K07P018_radius_le :
    (momentScalarGrow2622K07P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P018Expected]

end ConnesWeilRH.Dev
