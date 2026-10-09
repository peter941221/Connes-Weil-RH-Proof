import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P056 : ℚ := ((-35049221800212938590573738192422054925 : ℚ) / 960331529913699291233054453890285568)

def momentPanelGrowth2622K07P056 : ℚ := ((22576750794709836667994779115153355025 : ℚ) / 66100656852035245035030027202644148224)

theorem momentPanelPhase_owner2622K07P056 :
    (momentPanelPhase2622K07P056 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P056 :
    (momentPanelGrowth2622K07P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P056Input : RatPair2542 := (momentPanelPhase2622K07P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P056Expected : RatState2542 :=
  ((((18837880631189885121034963832296602863167022178760060224233471486965939861534561 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((382090912365955498179335778799747 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P056_replay :
    compactExp2620 momentScalarAmp2622K07P056Input 20 = momentScalarAmp2622K07P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K07P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P056_replay] at h
  simpa only [momentPanelPhase_owner2622K07P056] using h

theorem momentScalarAmp2622K07P056_radius_le :
    (momentScalarAmp2622K07P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P056Expected]

def momentScalarGrow2622K07P056Input : RatPair2542 := (momentPanelGrowth2622K07P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P056Expected : RatState2542 :=
  ((((375701020912330101542515443393804357934604545901018284764731188625239301018042593714041960559403 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3810059756281763658121443826934776795560655880971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P056_replay :
    compactExp2620 momentScalarGrow2622K07P056Input 20 = momentScalarGrow2622K07P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P056] using h

theorem momentScalarGrow2622K07P056_radius_le :
    (momentScalarGrow2622K07P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P056Expected]

end ConnesWeilRH.Dev
