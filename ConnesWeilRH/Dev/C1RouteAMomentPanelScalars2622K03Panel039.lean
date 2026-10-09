import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P039 : ℚ := ((-73346363125421600893569416258323198982921830264078025 : ℚ) / 1814636970450982335814650180421354904280297243672576)

def momentPanelGrowth2622K03P039 : ℚ := ((2809925368765408998475181706477435142853001845392798425 : ℚ) / 5000637556094336485534205319231518117746936119228891136)

theorem momentPanelPhase_owner2622K03P039 :
    (momentPanelPhase2622K03P039 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P039 :
    (momentPanelGrowth2622K03P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P039Input : RatPair2542 := (momentPanelPhase2622K03P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P039Expected : RatState2542 :=
  ((((5966477107485467163820313400562542683582708544512609031320441622782196363948033 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7563702255602501593296523609101 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P039_replay :
    compactExp2620 momentScalarAmp2622K03P039Input 20 = momentScalarAmp2622K03P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K03P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P039_replay] at h
  simpa only [momentPanelPhase_owner2622K03P039] using h

theorem momentScalarAmp2622K03P039_radius_le :
    (momentScalarAmp2622K03P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P039Expected]

def momentScalarGrow2622K03P039Input : RatPair2542 := (momentPanelGrowth2622K03P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P039Expected : RatState2542 :=
  ((((1873287848311066252403292332619417165839726045260576460598041740524457432672337600008898621971107 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2374673192765860750971965581713778279130102493091 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P039_replay :
    compactExp2620 momentScalarGrow2622K03P039Input 20 = momentScalarGrow2622K03P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P039] using h

theorem momentScalarGrow2622K03P039_radius_le :
    (momentScalarGrow2622K03P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P039Expected]

end ConnesWeilRH.Dev
