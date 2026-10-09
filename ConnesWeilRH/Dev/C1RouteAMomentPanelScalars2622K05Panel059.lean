import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P059 : ℚ := ((-821853420305016501457387160019872545897 : ℚ) / 24527517933695965043679410980179148800)

def momentPanelGrowth2622K05P059 : ℚ := ((6677307311548715060615099260014594358123 : ℚ) / 27619071316375932186134219138988087705600)

theorem momentPanelPhase_owner2622K05P059 :
    (momentPanelPhase2622K05P059 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-61 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P059, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P059 :
    (momentPanelGrowth2622K05P059 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P059, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P059Input : RatPair2542 := (momentPanelPhase2622K05P059 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P059Expected : RatState2542 :=
  ((((2995632455102095658595181584416465041182431739692443758472645351608563493998196759 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((7595073259787056497852918756001965 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P059_replay :
    compactExp2620 momentScalarAmp2622K05P059Input 20 = momentScalarAmp2622K05P059Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P059_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-61 / 200) 0) -
      (momentScalarAmp2622K05P059Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P059]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P059 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P059 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P059Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P059_replay] at h
  simpa only [momentPanelPhase_owner2622K05P059] using h

theorem momentScalarAmp2622K05P059_radius_le :
    (momentScalarAmp2622K05P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P059Expected]

def momentScalarGrow2622K05P059Input : RatPair2542 := (momentPanelGrowth2622K05P059 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P059Expected : RatState2542 :=
  ((((2720166847425757974345063183426077099851026804096609281956091680460894809576279821149051920991947 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3448220341823012222391620290778410732169904429671 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P059_replay :
    compactExp2620 momentScalarGrow2622K05P059Input 20 = momentScalarGrow2622K05P059Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P059_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P059Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P059]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P059 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P059 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P059Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P059_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P059] using h

theorem momentScalarGrow2622K05P059_radius_le :
    (momentScalarGrow2622K05P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P059Expected]

end ConnesWeilRH.Dev
