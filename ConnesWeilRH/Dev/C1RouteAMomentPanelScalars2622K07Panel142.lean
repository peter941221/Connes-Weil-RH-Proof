import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P142 : ℚ := ((-3495666499770851845040972269833274875 : ℚ) / 94029250922529144085419456961970176)

def momentPanelGrowth2622K07P142 : ℚ := ((486438402929849038734411462760173424025 : ℚ) / 699208770962564822717190855085170622464)

theorem momentPanelPhase_owner2622K07P142 :
    (momentPanelPhase2622K07P142 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P142 :
    (momentPanelGrowth2622K07P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P142Input : RatPair2542 := (momentPanelPhase2622K07P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P142Expected : RatState2542 :=
  ((((19099192215490784430973556056157021253785933222287446175927269657005228800289675 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((193695689419184221538615592901129 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P142_replay :
    compactExp2620 momentScalarAmp2622K07P142Input 20 = momentScalarAmp2622K07P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K07P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P142_replay] at h
  simpa only [momentPanelPhase_owner2622K07P142] using h

theorem momentScalarAmp2622K07P142_radius_le :
    (momentScalarAmp2622K07P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P142Expected]

def momentScalarGrow2622K07P142Input : RatPair2542 := (momentPanelGrowth2622K07P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P142Expected : RatState2542 :=
  ((((2141443302601153968855268614470058951669146931638580740332471941288498694240101035266756959807801 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5429200173683315864851133353448086114586659349187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P142_replay :
    compactExp2620 momentScalarGrow2622K07P142Input 20 = momentScalarGrow2622K07P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P142] using h

theorem momentScalarGrow2622K07P142_radius_le :
    (momentScalarGrow2622K07P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P142Expected]

end ConnesWeilRH.Dev
