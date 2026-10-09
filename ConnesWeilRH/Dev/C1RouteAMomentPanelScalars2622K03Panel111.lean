import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P111 : ℚ := ((-72927214918316099661686137582218181525096905404468825 : ℚ) / 2323239540242136551349532502206621395120561768628224)

def momentPanelGrowth2622K03P111 : ℚ := ((25629694968394796331626158040228085809263480699918475 : ℚ) / 172324470587606431726775438131650348867677535697108992)

theorem momentPanelPhase_owner2622K03P111 :
    (momentPanelPhase2622K03P111 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (43 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P111 :
    (momentPanelGrowth2622K03P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P111Input : RatPair2542 := (momentPanelPhase2622K03P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P111Expected : RatState2542 :=
  ((((24884513917869849865816750720708010405379572418497391336822046029672883618672838863 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15772906675583587866789937648488229 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P111_replay :
    compactExp2620 momentScalarAmp2622K03P111Input 20 = momentScalarAmp2622K03P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K03P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P111_replay] at h
  simpa only [momentPanelPhase_owner2622K03P111] using h

theorem momentScalarAmp2622K03P111_radius_le :
    (momentScalarAmp2622K03P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P111Expected]

def momentScalarGrow2622K03P111Input : RatPair2542 := (momentPanelGrowth2622K03P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P111Expected : RatState2542 :=
  ((((309813924013064264526797931313850288537330940311020325921157779219030943559137943281501521920469 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((785471502057714091895316860850006023310642515313 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P111_replay :
    compactExp2620 momentScalarGrow2622K03P111Input 20 = momentScalarGrow2622K03P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P111] using h

theorem momentScalarGrow2622K03P111_radius_le :
    (momentScalarGrow2622K03P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P111Expected]

end ConnesWeilRH.Dev
