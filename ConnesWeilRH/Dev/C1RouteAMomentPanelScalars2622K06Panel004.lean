import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P004 : ℚ := ((-61839789 : ℚ) / 537950)

def momentPanelGrowth2622K06P004 : ℚ := ((27016267 : ℚ) / 3531675)

theorem momentPanelPhase_owner2622K06P004 :
    (momentPanelPhase2622K06P004 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P004 :
    (momentPanelGrowth2622K06P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P004Input : RatPair2542 := (momentPanelPhase2622K06P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P004Expected : RatState2542 :=
  ((((1589867438699587447194034004299929017812411833 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P004_replay :
    compactExp2620 momentScalarAmp2622K06P004Input 20 = momentScalarAmp2622K06P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K06P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P004_replay] at h
  simpa only [momentPanelPhase_owner2622K06P004] using h

theorem momentScalarAmp2622K06P004_radius_le :
    (momentScalarAmp2622K06P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P004Expected]

def momentScalarGrow2622K06P004Input : RatPair2542 := (momentPanelGrowth2622K06P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P004Expected : RatState2542 :=
  ((((4485622059506127427677541839551885071208936486848154210959100137329342389829306683453921576091289043 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5686160013588413309297982126783084122696220453858889 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P004_replay :
    compactExp2620 momentScalarGrow2622K06P004Input 20 = momentScalarGrow2622K06P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P004] using h

theorem momentScalarGrow2622K06P004_radius_le :
    (momentScalarGrow2622K06P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P004Expected]

end ConnesWeilRH.Dev
