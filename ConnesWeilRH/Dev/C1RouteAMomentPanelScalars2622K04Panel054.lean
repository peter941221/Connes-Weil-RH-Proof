import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P054 : ℚ := ((-125362426539013283733262609047482647080554498226634301 : ℚ) / 3326343472620510098794441280398993364853629281894400)

def momentPanelGrowth2622K04P054 : ℚ := ((15666273104836093947390160625028600662621211594303 : ℚ) / 41247458319202240562584464517090409441461377433600)

theorem momentPanelPhase_owner2622K04P054 :
    (momentPanelPhase2622K04P054 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P054 :
    (momentPanelGrowth2622K04P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P054Input : RatPair2542 := (momentPanelPhase2622K04P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P054Expected : RatState2542 :=
  ((((5726555346638773363868011607182613590623640938821002844229599859511965354494681 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((116152518237229635003837528569611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P054_replay :
    compactExp2620 momentScalarAmp2622K04P054Input 20 = momentScalarAmp2622K04P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K04P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P054_replay] at h
  simpa only [momentPanelPhase_owner2622K04P054] using h

theorem momentScalarAmp2622K04P054_radius_le :
    (momentScalarAmp2622K04P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P054Expected]

def momentScalarGrow2622K04P054Input : RatPair2542 := (momentPanelGrowth2622K04P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P054Expected : RatState2542 :=
  ((((1561416641604114878547742122825493347163563668566230715522111516844798144026932252612918238260907 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1979330025989087605371691538925463094961418389865 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P054_replay :
    compactExp2620 momentScalarGrow2622K04P054Input 20 = momentScalarGrow2622K04P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P054] using h

theorem momentScalarGrow2622K04P054_radius_le :
    (momentScalarGrow2622K04P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P054Expected]

end ConnesWeilRH.Dev
