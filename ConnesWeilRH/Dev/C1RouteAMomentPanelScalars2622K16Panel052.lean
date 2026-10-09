import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P052 : ℚ := ((-31672102185112205075216949277377753 : ℚ) / 892426022560673498653679056584704)

def momentPanelGrowth2622K16P052 : ℚ := ((505661623148941341818969577757016819483 : ℚ) / 1546642243169819406262746028353100185600)

theorem momentPanelPhase_owner2622K16P052 :
    (momentPanelPhase2622K16P052 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-3 / 8) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P052, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P052 :
    (momentPanelGrowth2622K16P052 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (-3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P052, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P052Input : RatPair2542 := (momentPanelPhase2622K16P052 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P052Expected : RatState2542 :=
  ((((825153654239697433806754558471769082105295776010693548340781174500160195206988241 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1046041931019429252467182262896775 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K16P052_replay :
    compactExp2620 momentScalarAmp2622K16P052Input 20 = momentScalarAmp2622K16P052Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P052_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-3 / 8) 0) -
      (momentScalarAmp2622K16P052Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P052]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P052 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P052 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P052Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P052_replay] at h
  simpa only [momentPanelPhase_owner2622K16P052] using h

theorem momentScalarAmp2622K16P052_radius_le :
    (momentScalarAmp2622K16P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P052Expected]

def momentScalarGrow2622K16P052Input : RatPair2542 := (momentPanelGrowth2622K16P052 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P052Expected : RatState2542 :=
  ((((1481008431264614053748129572366458767325551140197181997802533016670991983540912736622953145876747 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3754801282939988585949034752597930423555920077655 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K16P052_replay :
    compactExp2620 momentScalarGrow2622K16P052Input 20 = momentScalarGrow2622K16P052Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P052_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P052Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P052Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P052 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P052]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P052 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P052 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P052Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P052Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P052_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P052] using h

theorem momentScalarGrow2622K16P052_radius_le :
    (momentScalarGrow2622K16P052Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P052Expected]

end ConnesWeilRH.Dev
