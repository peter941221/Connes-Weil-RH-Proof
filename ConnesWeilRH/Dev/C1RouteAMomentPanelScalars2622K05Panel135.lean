import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P135 : ℚ := ((-797526897610596051058365944499287206273 : ℚ) / 21444591673940911139239428784704716800)

def momentPanelGrowth2622K05P135 : ℚ := ((601651609947925983528064538526207777283 : ℚ) / 1313232273450995983023961060553628057600)

theorem momentPanelPhase_owner2622K05P135 :
    (momentPanelPhase2622K05P135 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (91 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P135, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P135 :
    (momentPanelGrowth2622K05P135 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P135, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P135Input : RatPair2542 := (momentPanelPhase2622K05P135 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P135Expected : RatState2542 :=
  ((((18838466194171934979595542416270146803430073100046998164576385734619460493726115 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((191051522199076945024189901474167 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P135_replay :
    compactExp2620 momentScalarAmp2622K05P135Input 20 = momentScalarAmp2622K05P135Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P135_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (91 / 200) 0) -
      (momentScalarAmp2622K05P135Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P135]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P135 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P135 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P135Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P135_replay] at h
  simpa only [momentPanelPhase_owner2622K05P135] using h

theorem momentScalarAmp2622K05P135_radius_le :
    (momentScalarAmp2622K05P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P135Expected]

def momentScalarGrow2622K05P135Input : RatPair2542 := (momentPanelGrowth2622K05P135 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P135Expected : RatState2542 :=
  ((((3377292890355443974373253665004646175933415644753054008469694307618998822745396738335158225137035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4281225489044849009226926615975558703916952573453 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P135_replay :
    compactExp2620 momentScalarGrow2622K05P135Input 20 = momentScalarGrow2622K05P135Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P135_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P135Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P135]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P135 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P135 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P135Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P135_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P135] using h

theorem momentScalarGrow2622K05P135_radius_le :
    (momentScalarGrow2622K05P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P135Expected]

end ConnesWeilRH.Dev
