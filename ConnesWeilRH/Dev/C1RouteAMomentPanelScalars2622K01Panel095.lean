import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P095 : ℚ := ((-28535238617473620089299362143197241264330407401613121 : ℚ) / 948620178957016234945389769594606942396792543641600)

def momentPanelGrowth2622K01P095 : ℚ := ((8440541513847236534305463059530304238890175763583113 : ℚ) / 221404688507589756117925754039941068259024745109913600)

theorem momentPanelPhase_owner2622K01P095 :
    (momentPanelPhase2622K01P095 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (11 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P095, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P095 :
    (momentPanelGrowth2622K01P095 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P095, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P095Input : RatPair2542 := (momentPanelPhase2622K01P095 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P095Expected : RatState2542 :=
  ((((46091427296827735978744107604079553966875828400624107081389941112217603018270731857 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((233718006550845821638379545845335535 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P095_replay :
    compactExp2620 momentScalarAmp2622K01P095Input 20 = momentScalarAmp2622K01P095Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P095_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (11 / 200) 0) -
      (momentScalarAmp2622K01P095Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P095]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P095 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P095 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P095Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P095_replay] at h
  simpa only [momentPanelPhase_owner2622K01P095] using h

theorem momentScalarAmp2622K01P095_radius_le :
    (momentScalarAmp2622K01P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P095Expected]

def momentScalarGrow2622K01P095Input : RatPair2542 := (momentPanelGrowth2622K01P095 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P095Expected : RatState2542 :=
  ((((2218988670330806955406388935929095449768388169650443581925322885897612320935803548457658998978341 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2812902217576849799577774451791280584006108772059 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P095_replay :
    compactExp2620 momentScalarGrow2622K01P095Input 20 = momentScalarGrow2622K01P095Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P095_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P095Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P095Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P095 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P095]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P095 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P095 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P095Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P095Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P095_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P095] using h

theorem momentScalarGrow2622K01P095_radius_le :
    (momentScalarGrow2622K01P095Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P095Expected]

end ConnesWeilRH.Dev
