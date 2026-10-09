import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P175 : ℚ := ((-58160211 : ℚ) / 537950)

def momentPanelGrowth2622K06P175 : ℚ := ((27016267 : ℚ) / 3531675)

theorem momentPanelPhase_owner2622K06P175 :
    (momentPanelPhase2622K06P175 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (171 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P175, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P175 :
    (momentPanelGrowth2622K06P175 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P175, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P175Input : RatPair2542 := (momentPanelPhase2622K06P175 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P175Expected : RatState2542 :=
  ((((11885710776996185277273468796606823690205172637117 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412399 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P175_replay :
    compactExp2620 momentScalarAmp2622K06P175Input 20 = momentScalarAmp2622K06P175Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P175_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (171 / 200) 0) -
      (momentScalarAmp2622K06P175Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P175]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P175 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P175 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P175Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P175_replay] at h
  simpa only [momentPanelPhase_owner2622K06P175] using h

theorem momentScalarAmp2622K06P175_radius_le :
    (momentScalarAmp2622K06P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P175Expected]

def momentScalarGrow2622K06P175Input : RatPair2542 := (momentPanelGrowth2622K06P175 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P175Expected : RatState2542 :=
  ((((4485622059506127427677541839551885071208936486848154210959100137329342389829306683453921576091289043 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5686160013588413309297982126783084122696220453858889 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P175_replay :
    compactExp2620 momentScalarGrow2622K06P175Input 20 = momentScalarGrow2622K06P175Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P175_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P175Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P175]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P175 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P175 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P175Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P175_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P175] using h

theorem momentScalarGrow2622K06P175_radius_le :
    (momentScalarGrow2622K06P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P175Expected]

end ConnesWeilRH.Dev
