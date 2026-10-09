import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K11
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K11P126 : ℚ := ((-798045255607162551064538407117462424091 : ℚ) / 23440380778940235508955838311248691200)

def momentPanelGrowth2622K11P126 : ℚ := ((7894510649808434896620428507591849036803 : ℚ) / 25182018108039562074674413213465549209600)

theorem momentPanelPhase_owner2622K11P126 :
    (momentPanelPhase2622K11P126 : ℝ) = momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (73 / 200) 0 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K11P126 :
    (momentPanelGrowth2622K11P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K11P126Input : RatPair2542 := (momentPanelPhase2622K11P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K11P126Expected : RatState2542 :=
  ((((3497187288521973835420176939811894929879449107426470787030016850549927798644649303 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4433355510128117459939486107688467 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K11P126_replay :
    compactExp2620 momentScalarAmp2622K11P126Input 20 = momentScalarAmp2622K11P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K11P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K11P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K11P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K11P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K11P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K11P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K11P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K11P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K11P126_replay] at h
  simpa only [momentPanelPhase_owner2622K11P126] using h

theorem momentScalarAmp2622K11P126_radius_le :
    (momentScalarAmp2622K11P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarAmp2622K11P126Expected]

def momentScalarGrow2622K11P126Input : RatPair2542 := (momentPanelGrowth2622K11P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K11P126Expected : RatState2542 :=
  ((((1461231546501442328211713903466092664866829543243806225425732881126522665471697360511245082197491 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3704660986389037870216215227656245111664236503169 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K11P126_replay :
    compactExp2620 momentScalarGrow2622K11P126Input 20 = momentScalarGrow2622K11P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K11P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K11P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K11P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K11P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K11P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K11P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K11P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K11P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K11P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K11P126] using h

theorem momentScalarGrow2622K11P126_radius_le :
    (momentScalarGrow2622K11P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarGrow2622K11P126Expected]

end ConnesWeilRH.Dev
