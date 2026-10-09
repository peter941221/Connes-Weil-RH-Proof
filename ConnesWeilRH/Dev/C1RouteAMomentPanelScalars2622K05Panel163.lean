import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P163 : ℚ := ((-2395198967974503370728881142645394133547 : ℚ) / 37301379502075787076681389840112025600)

def momentPanelGrowth2622K05P163 : ℚ := ((944163582889848880085745927957343515443 : ℚ) / 432407789183611239852779831704525209600)

theorem momentPanelPhase_owner2622K05P163 :
    (momentPanelPhase2622K05P163 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P163 :
    (momentPanelGrowth2622K05P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P163Input : RatPair2542 := (momentPanelPhase2622K05P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P163Expected : RatState2542 :=
  ((((138553943686591509778232569592317185903729506132893859454665359914097 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2418202936720958635037971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P163_replay :
    compactExp2620 momentScalarAmp2622K05P163Input 20 = momentScalarAmp2622K05P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K05P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P163_replay] at h
  simpa only [momentPanelPhase_owner2622K05P163] using h

theorem momentScalarAmp2622K05P163_radius_le :
    (momentScalarAmp2622K05P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P163Expected]

def momentScalarGrow2622K05P163Input : RatPair2542 := (momentPanelGrowth2622K05P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P163Expected : RatState2542 :=
  ((((18961897474268068227011813347704842439151808266729199303369586587785199675934888086890393936200519 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24037010661189699347486798153818141093729724144469 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P163_replay :
    compactExp2620 momentScalarGrow2622K05P163Input 20 = momentScalarGrow2622K05P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P163] using h

theorem momentScalarGrow2622K05P163_radius_le :
    (momentScalarGrow2622K05P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P163Expected]

end ConnesWeilRH.Dev
