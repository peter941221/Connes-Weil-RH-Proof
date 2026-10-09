import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P071 : ℚ := ((-20476449 : ℚ) / 643850)

def momentPanelGrowth2622K06P071 : ℚ := ((125970107 : ℚ) / 774252675)

theorem momentPanelPhase_owner2622K06P071 :
    (momentPanelPhase2622K06P071 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-37 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P071, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P071 :
    (momentPanelGrowth2622K06P071 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P071, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P071Input : RatPair2542 := (momentPanelPhase2622K06P071 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P071Expected : RatState2542 :=
  ((((32936103374271150641349810623321051173662630236073843073490051662080992705270836635 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((41752737548378872676934941909910003 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P071_replay :
    compactExp2620 momentScalarAmp2622K06P071Input 20 = momentScalarAmp2622K06P071Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P071_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-37 / 200) 0) -
      (momentScalarAmp2622K06P071Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P071]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P071 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P071 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P071Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P071_replay] at h
  simpa only [momentPanelPhase_owner2622K06P071] using h

theorem momentScalarAmp2622K06P071_radius_le :
    (momentScalarAmp2622K06P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P071Expected]

def momentScalarGrow2622K06P071Input : RatPair2542 := (momentPanelGrowth2622K06P071 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P071Expected : RatState2542 :=
  ((((157086148446753352052558444542639019500357808394935146538850269556668518349419215322991051502051 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3186085111498273127581758865580202025326335958095 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P071_replay :
    compactExp2620 momentScalarGrow2622K06P071Input 20 = momentScalarGrow2622K06P071Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P071_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P071Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P071]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P071 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P071 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P071Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P071_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P071] using h

theorem momentScalarGrow2622K06P071_radius_le :
    (momentScalarGrow2622K06P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P071Expected]

end ConnesWeilRH.Dev
