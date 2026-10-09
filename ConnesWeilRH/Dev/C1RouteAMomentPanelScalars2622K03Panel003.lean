import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P003 : ℚ := ((-73232123725401811183959882388204649725960690817391425 : ℚ) / 613282624564980137051221247928570262123120693346304)

def momentPanelGrowth2622K03P003 : ℚ := ((4769747132729459171418867494959822251851324153544616425 : ℚ) / 539820336108394635049145417542388340907803972569399296)

theorem momentPanelPhase_owner2622K03P003 :
    (momentPanelPhase2622K03P003 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-173 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P003 :
    (momentPanelGrowth2622K03P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P003Input : RatPair2542 := (momentPanelPhase2622K03P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P003Expected : RatState2542 :=
  ((((36929404302407992548824025326439868511830783 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P003_replay :
    compactExp2620 momentScalarAmp2622K03P003Input 20 = momentScalarAmp2622K03P003Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622K03P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P003]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P003 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P003_replay] at h
  simpa only [momentPanelPhase_owner2622K03P003] using h

theorem momentScalarAmp2622K03P003_radius_le :
    (momentScalarAmp2622K03P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P003Expected]

def momentScalarGrow2622K03P003Input : RatPair2542 := (momentPanelGrowth2622K03P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P003Expected : RatState2542 :=
  ((((7343614950754398189760734484865118316419153591451738735616716759021842269980822598825669654269280363 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((18618118914467528439129499934417532081086389231014129 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P003_replay :
    compactExp2620 momentScalarGrow2622K03P003Input 20 = momentScalarGrow2622K03P003Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P003_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P003] using h

theorem momentScalarGrow2622K03P003_radius_le :
    (momentScalarGrow2622K03P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P003Expected]

end ConnesWeilRH.Dev
