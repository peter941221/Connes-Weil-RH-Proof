import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K23
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K23P127 : ℚ := ((-30635460117305726467149006673263399 : ℚ) / 892426022560673498653679056584704)

def momentPanelGrowth2622K23P127 : ℚ := ((505661623148941341818969577757016819483 : ℚ) / 1546642243169819406262746028353100185600)

theorem momentPanelPhase_owner2622K23P127 :
    (momentPanelPhase2622K23P127 : ℝ) = momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K23P127 :
    (momentPanelGrowth2622K23P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K23P127Input : RatPair2542 := (momentPanelPhase2622K23P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K23P127Expected : RatState2542 :=
  ((((1318199983360970364774599193112084166223366805145352071192341681924815531830016123 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((835535854001495980760002468459935 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K23P127_replay :
    compactExp2620 momentScalarAmp2622K23P127Input 20 = momentScalarAmp2622K23P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K23P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K23P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K23P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K23P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K23P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K23P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K23P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K23P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K23P127_replay] at h
  simpa only [momentPanelPhase_owner2622K23P127] using h

theorem momentScalarAmp2622K23P127_radius_le :
    (momentScalarAmp2622K23P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarAmp2622K23P127Expected]

def momentScalarGrow2622K23P127Input : RatPair2542 := (momentPanelGrowth2622K23P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K23P127Expected : RatState2542 :=
  ((((1481008431264614053748129572366458767325551140197181997802533016670991983540912736622953145876747 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3754801282939988585949034752597930423555920077655 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K23P127_replay :
    compactExp2620 momentScalarGrow2622K23P127Input 20 = momentScalarGrow2622K23P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K23P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K23P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K23P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K23P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K23P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K23P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K23P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K23P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K23P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K23P127] using h

theorem momentScalarGrow2622K23P127_radius_le :
    (momentScalarGrow2622K23P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarGrow2622K23P127Expected]

end ConnesWeilRH.Dev
