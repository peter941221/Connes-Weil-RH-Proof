import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P125 : ℚ := ((-799455770340793900887276885111603181693 : ℚ) / 23635091911135291545025731923594444800)

def momentPanelGrowth2622K05P125 : ℚ := ((87696909166284452133041099075774721 : ℚ) / 293080818772766637626037781082931200)

theorem momentPanelPhase_owner2622K05P125 :
    (momentPanelPhase2622K05P125 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (71 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P125, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P125 :
    (momentPanelGrowth2622K05P125 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P125, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P125Input : RatPair2542 := (momentPanelPhase2622K05P125 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P125Expected : RatState2542 :=
  ((((272577546739905114472467136180061263583313315095230198299746289186990055049208375 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2764353898125259752638032525069787 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P125_replay :
    compactExp2620 momentScalarAmp2622K05P125Input 20 = momentScalarAmp2622K05P125Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P125_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (71 / 200) 0) -
      (momentScalarAmp2622K05P125Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P125]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P125 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P125 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P125Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P125_replay] at h
  simpa only [momentPanelPhase_owner2622K05P125] using h

theorem momentScalarAmp2622K05P125_radius_le :
    (momentScalarAmp2622K05P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P125Expected]

def momentScalarGrow2622K05P125Input : RatPair2542 := (momentPanelGrowth2622K05P125 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P125Expected : RatState2542 :=
  ((((2881045281709214139916397964432890900071303158812460953434269332195650998905430951062616161628049 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3652157738454198456492072446109540595968949795797 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P125_replay :
    compactExp2620 momentScalarGrow2622K05P125Input 20 = momentScalarGrow2622K05P125Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P125_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P125Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P125Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P125 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P125]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P125 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P125 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P125Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P125Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P125_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P125] using h

theorem momentScalarGrow2622K05P125_radius_le :
    (momentScalarGrow2622K05P125Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P125Expected]

end ConnesWeilRH.Dev
