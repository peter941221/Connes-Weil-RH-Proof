import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P053 : ℚ := ((-824547512684971082851241695763817575909 : ℚ) / 23440380778940235508955838311248691200)

def momentPanelGrowth2622K25P053 : ℚ := ((7894510649808434896620428507591849036803 : ℚ) / 25182018108039562074674413213465549209600)

theorem momentPanelPhase_owner2622K25P053 :
    (momentPanelPhase2622K25P053 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P053 :
    (momentPanelGrowth2622K25P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P053Input : RatPair2542 := (momentPanelPhase2622K25P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P053Expected : RatState2542 :=
  ((((1129003080358540227121539103615903755072945580802155701360518604989752334734169277 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((715614723628838174132423765621439 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K25P053_replay :
    compactExp2620 momentScalarAmp2622K25P053Input 20 = momentScalarAmp2622K25P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K25P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P053_replay] at h
  simpa only [momentPanelPhase_owner2622K25P053] using h

theorem momentScalarAmp2622K25P053_radius_le :
    (momentScalarAmp2622K25P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P053Expected]

def momentScalarGrow2622K25P053Input : RatPair2542 := (momentPanelGrowth2622K25P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P053Expected : RatState2542 :=
  ((((1461231546501442328211713903466092664866829543243806225425732881126522665471697360511245082197491 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3704660986389037870216215227656245111664236503169 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K25P053_replay :
    compactExp2620 momentScalarGrow2622K25P053Input 20 = momentScalarGrow2622K25P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P053] using h

theorem momentScalarGrow2622K25P053_radius_le :
    (momentScalarGrow2622K25P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P053Expected]

end ConnesWeilRH.Dev
