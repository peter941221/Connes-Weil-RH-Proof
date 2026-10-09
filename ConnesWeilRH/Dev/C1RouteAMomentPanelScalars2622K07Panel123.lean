import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P123 : ℚ := ((-29854488931472406766057465922829145075 : ℚ) / 960331529913699291233054453890285568)

def momentPanelGrowth2622K07P123 : ℚ := ((22576750794709836667994779115153355025 : ℚ) / 66100656852035245035030027202644148224)

theorem momentPanelPhase_owner2622K07P123 :
    (momentPanelPhase2622K07P123 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (67 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P123 :
    (momentPanelGrowth2622K07P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P123Input : RatPair2542 := (momentPanelPhase2622K07P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P123Expected : RatState2542 :=
  ((((67357564515740637338933192674309424157550405876561552516941798822419554601832130283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((85388388608125815040211470083464945 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P123_replay :
    compactExp2620 momentScalarAmp2622K07P123Input 20 = momentScalarAmp2622K07P123Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622K07P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P123]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P123 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P123_replay] at h
  simpa only [momentPanelPhase_owner2622K07P123] using h

theorem momentScalarAmp2622K07P123_radius_le :
    (momentScalarAmp2622K07P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P123Expected]

def momentScalarGrow2622K07P123Input : RatPair2542 := (momentPanelGrowth2622K07P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P123Expected : RatState2542 :=
  ((((375701020912330101542515443393804357934604545901018284764731188625239301018042593714041960559403 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3810059756281763658121443826934776795560655880971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P123_replay :
    compactExp2620 momentScalarGrow2622K07P123Input 20 = momentScalarGrow2622K07P123Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P123_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P123] using h

theorem momentScalarGrow2622K07P123_radius_le :
    (momentScalarGrow2622K07P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P123Expected]

end ConnesWeilRH.Dev
