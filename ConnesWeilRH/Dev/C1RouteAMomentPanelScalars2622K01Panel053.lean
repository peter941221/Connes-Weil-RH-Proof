import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P053 : ℚ := ((-28601007732535346832383536150666811030793509531195453 : ℚ) / 824735079230138917269530547446390764558770136678400)

def momentPanelGrowth2622K01P053 : ℚ := ((265690651159485705357951298174925976839122746345260651 : ℚ) / 886013495060969175325806711601764767153444038587187200)

theorem momentPanelPhase_owner2622K01P053 :
    (momentPanelPhase2622K01P053 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P053 :
    (momentPanelGrowth2622K01P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P053Input : RatPair2542 := (momentPanelPhase2622K01P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P053Expected : RatState2542 :=
  ((((1856477905784479816185558198403406618372183608180640256306760206925554197193898257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2353443166945396601590309056830785 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P053_replay :
    compactExp2620 momentScalarAmp2622K01P053Input 20 = momentScalarAmp2622K01P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K01P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P053_replay] at h
  simpa only [momentPanelPhase_owner2622K01P053] using h

theorem momentScalarAmp2622K01P053_radius_le :
    (momentScalarAmp2622K01P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P053Expected]

def momentScalarGrow2622K01P053Input : RatPair2542 := (momentPanelGrowth2622K01P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P053Expected : RatState2542 :=
  ((((720727979303193346397734925515207310140729147029871287212336094689757413832054565534971155341121 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3654523977138101922376630874382873001361378544207 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P053_replay :
    compactExp2620 momentScalarGrow2622K01P053Input 20 = momentScalarGrow2622K01P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P053] using h

theorem momentScalarGrow2622K01P053_radius_le :
    (momentScalarGrow2622K01P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P053Expected]

end ConnesWeilRH.Dev
