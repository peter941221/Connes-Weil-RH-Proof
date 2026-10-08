import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P064 : ℚ := ((-368319112661825967898624722583218256317019404073294923 : ℚ) / 10675527291902038718339767394288333721115668198195200)

def momentPanelGrowth2622K04P064 : ℚ := ((70865493993026807897250019826292110305288478025781549 : ℚ) / 258501246680902935909431379014932274757965770968268800)

theorem momentPanelPhase_owner2622K04P064 :
    (momentPanelPhase2622K04P064 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P064 :
    (momentPanelGrowth2622K04P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P064Input : RatPair2542 := (momentPanelPhase2622K04P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P064Expected : RatState2542 :=
  ((((1108824985617161635628272271068956275070636392745432968304239108438392533774185227 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((702824454513756371650890195196973 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P064_replay :
    compactExp2620 momentScalarAmp2622K04P064Input 20 = momentScalarAmp2622K04P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K04P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P064_replay] at h
  simpa only [momentPanelPhase_owner2622K04P064] using h

theorem momentScalarAmp2622K04P064_radius_le :
    (momentScalarAmp2622K04P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P064Expected]

def momentScalarGrow2622K04P064Input : RatPair2542 := (momentPanelGrowth2622K04P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P064Expected : RatState2542 :=
  ((((1404837341732253631190077664669650216109375544589649260319851117093322980406836239065230368229457 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3561684867772338976107249691213091090660970172877 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P064_replay :
    compactExp2620 momentScalarGrow2622K04P064Input 20 = momentScalarGrow2622K04P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P064] using h

theorem momentScalarGrow2622K04P064_radius_le :
    (momentScalarGrow2622K04P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P064Expected]

end ConnesWeilRH.Dev
