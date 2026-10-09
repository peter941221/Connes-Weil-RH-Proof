import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P082 : ℚ := ((-8775463087826505868734293296820287018542919750118625 : ℚ) / 290656138124183317857757821106450785534073584484352)

def momentPanelGrowth2622K03P082 : ℚ := ((605659089945588869675053557244588978767208915968475 : ℚ) / 11741978185873473589145567136948752082981947537620992)

theorem momentPanelPhase_owner2622K03P082 :
    (momentPanelPhase2622K03P082 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P082, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P082 :
    (momentPanelGrowth2622K03P082 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P082, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P082Input : RatPair2542 := (momentPanelPhase2622K03P082 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P082Expected : RatState2542 :=
  ((((82487855611479051434631877110037282943271159341307262555006080172320147460490684257 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((209137581020459777166186376385140349 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P082_replay :
    compactExp2620 momentScalarAmp2622K03P082Input 20 = momentScalarAmp2622K03P082Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P082_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 40) 0) -
      (momentScalarAmp2622K03P082Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P082]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P082 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P082 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P082Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P082_replay] at h
  simpa only [momentPanelPhase_owner2622K03P082] using h

theorem momentScalarAmp2622K03P082_radius_le :
    (momentScalarAmp2622K03P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P082Expected]

def momentScalarGrow2622K03P082Input : RatPair2542 := (momentPanelGrowth2622K03P082 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P082Expected : RatState2542 :=
  ((((1124526817119531067869752588346192782199023421460336589007263071122836526198218462511709394847941 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2851014049143938379348354530546278063960943096297 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P082_replay :
    compactExp2620 momentScalarGrow2622K03P082Input 20 = momentScalarGrow2622K03P082Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P082_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P082Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P082]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P082 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P082 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P082Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P082_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P082] using h

theorem momentScalarGrow2622K03P082_radius_le :
    (momentScalarGrow2622K03P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P082Expected]

end ConnesWeilRH.Dev
