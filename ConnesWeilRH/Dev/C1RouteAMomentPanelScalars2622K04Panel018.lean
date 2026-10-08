import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P018 : ℚ := ((-126775764191121724678796282565159387333886758494845637 : ℚ) / 1860274642672948108971369932580471960761271949721600)

def momentPanelGrowth2622K04P018 : ℚ := ((25309364953448694388565640557111809721196781654724727 : ℚ) / 12931006820685267118376176711809370885141322688102400)

theorem momentPanelPhase_owner2622K04P018 :
    (momentPanelPhase2622K04P018 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-143 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P018, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P018 :
    (momentPanelGrowth2622K04P018 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-143 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P018, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P018Input : RatPair2542 := (momentPanelPhase2622K04P018 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P018Expected : RatState2542 :=
  ((((337882393198636851682513774384044832065287188265369338261527965887 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1208929246371885619660237 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P018_replay :
    compactExp2620 momentScalarAmp2622K04P018Input 20 = momentScalarAmp2622K04P018Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P018_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-143 / 200) 0) -
      (momentScalarAmp2622K04P018Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P018]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P018 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P018 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P018Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P018_replay] at h
  simpa only [momentPanelPhase_owner2622K04P018] using h

theorem momentScalarAmp2622K04P018_radius_le :
    (momentScalarAmp2622K04P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P018Expected]

def momentScalarGrow2622K04P018Input : RatPair2542 := (momentPanelGrowth2622K04P018 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P018Expected : RatState2542 :=
  ((((15122604256843315140376888783107517981110781502877550261127761438647296352514924261257937472555747 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19170142580366679705113331605451398491729434165781 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P018_replay :
    compactExp2620 momentScalarGrow2622K04P018Input 20 = momentScalarGrow2622K04P018Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P018_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-143 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P018Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P018Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P018 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P018]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P018 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P018 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P018Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P018Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P018_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P018] using h

theorem momentScalarGrow2622K04P018_radius_le :
    (momentScalarGrow2622K04P018Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P018Expected]

end ConnesWeilRH.Dev
