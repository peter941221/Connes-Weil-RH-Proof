import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P078 : ℚ := ((-118269895749295505798801911264720188188574062144233997 : ℚ) / 3755659578586462831016773700009401501877559466393600)

def momentPanelGrowth2622K04P078 : ℚ := ((142857015055999983794630777972186466796840778486583 : ℚ) / 846215157005363613479457751286605666361330473369600)

theorem momentPanelPhase_owner2622K04P078 :
    (momentPanelPhase2622K04P078 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P078 :
    (momentPanelGrowth2622K04P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P078Input : RatPair2542 := (momentPanelPhase2622K04P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P078Expected : RatState2542 :=
  ((((22498446120753608243027409504108174230716493599058320277239987616732203526134265947 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((57042050536996992286867509551764817 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P078_replay :
    compactExp2620 momentScalarAmp2622K04P078Input 20 = momentScalarAmp2622K04P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K04P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P078_replay] at h
  simpa only [momentPanelPhase_owner2622K04P078] using h

theorem momentScalarAmp2622K04P078_radius_le :
    (momentScalarAmp2622K04P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P078Expected]

def momentScalarGrow2622K04P078Input : RatPair2542 := (momentPanelGrowth2622K04P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P078Expected : RatState2542 :=
  ((((1264403483818292412025331243736281502269558147766466385022209726429020429867412430180841335424401 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3205643154283219137301644122467077721735874924331 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P078_replay :
    compactExp2620 momentScalarGrow2622K04P078Input 20 = momentScalarGrow2622K04P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P078] using h

theorem momentScalarGrow2622K04P078_radius_le :
    (momentScalarGrow2622K04P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P078Expected]

end ConnesWeilRH.Dev
