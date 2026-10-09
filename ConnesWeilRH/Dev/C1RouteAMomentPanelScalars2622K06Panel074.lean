import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P074 : ℚ := ((-20403403 : ℚ) / 650650)

def momentPanelGrowth2622K06P074 : ℚ := ((436127 : ℚ) / 3090675)

theorem momentPanelPhase_owner2622K06P074 :
    (momentPanelPhase2622K06P074 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P074 :
    (momentPanelGrowth2622K06P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P074Input : RatPair2542 := (momentPanelPhase2622K06P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P074Expected : RatState2542 :=
  ((((3211134326529820860459990346419779512616780581415828442158298956628153487693878935 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((65131489484877996785216516972552665 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P074_replay :
    compactExp2620 momentScalarAmp2622K06P074Input 20 = momentScalarAmp2622K06P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K06P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P074_replay] at h
  simpa only [momentPanelPhase_owner2622K06P074] using h

theorem momentScalarAmp2622K06P074_radius_le :
    (momentScalarAmp2622K06P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P074Expected]

def momentScalarGrow2622K06P074Input : RatPair2542 := (momentPanelGrowth2622K06P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P074Expected : RatState2542 :=
  ((((307462518227428793000634190487020715460142624067652794264083485664205643285279587541082047839261 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3118039946623719374066048213771104624354049726921 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P074_replay :
    compactExp2620 momentScalarGrow2622K06P074Input 20 = momentScalarGrow2622K06P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P074] using h

theorem momentScalarGrow2622K06P074_radius_le :
    (momentScalarGrow2622K06P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P074Expected]

end ConnesWeilRH.Dev
