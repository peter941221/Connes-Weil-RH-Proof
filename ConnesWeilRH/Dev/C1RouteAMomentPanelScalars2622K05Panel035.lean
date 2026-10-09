import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P035 : ℚ := ((-825917591498164640541920804172179564473 : ℚ) / 19010702521502710688365758630382796800)

def momentPanelGrowth2622K05P035 : ℚ := ((18219854927622756287888480790899916283 : ℚ) / 26313384099297494624507966455912857600)

theorem momentPanelPhase_owner2622K05P035 :
    (momentPanelPhase2622K05P035 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P035 :
    (momentPanelGrowth2622K05P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P035Input : RatPair2542 := (momentPanelPhase2622K05P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P035Expected : RatState2542 :=
  ((((144776879169492485697160642674436827661367454632906108167307184151230689300535 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((367070621559071886939892885689 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P035_replay :
    compactExp2620 momentScalarAmp2622K05P035Input 20 = momentScalarAmp2622K05P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K05P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P035_replay] at h
  simpa only [momentPanelPhase_owner2622K05P035] using h

theorem momentScalarAmp2622K05P035_radius_le :
    (momentScalarAmp2622K05P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P035Expected]

def momentScalarGrow2622K05P035Input : RatPair2542 := (momentPanelGrowth2622K05P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P035Expected : RatState2542 :=
  ((((4268859215565671083568021771225711857201742924372015675337781451461166783811302880517397177518123 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5411418373518759356902781638685804781083093129057 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P035_replay :
    compactExp2620 momentScalarGrow2622K05P035Input 20 = momentScalarGrow2622K05P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P035] using h

theorem momentScalarGrow2622K05P035_radius_le :
    (momentScalarGrow2622K05P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P035Expected]

end ConnesWeilRH.Dev
