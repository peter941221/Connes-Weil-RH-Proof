import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P090 : ℚ := ((-113999607026572021883113641948401046361257792939699509 : ℚ) / 3805898697369712618830025366134023730678232147558400)

def momentPanelGrowth2622K04P090 : ℚ := ((478987089979701204362863701662069009799606947589879509 : ℚ) / 4756540858132985387138910409461549772834738128342220800)

theorem momentPanelPhase_owner2622K04P090 :
    (momentPanelPhase2622K04P090 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P090, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P090 :
    (momentPanelGrowth2622K04P090 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P090, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P090Input : RatPair2542 := (momentPanelPhase2622K04P090 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P090Expected : RatState2542 :=
  ((((104706144968656174808054715212509381523879078354003066341804128512402239118333600831 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((265469198265283931075743574887213509 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P090_replay :
    compactExp2620 momentScalarAmp2622K04P090Input 20 = momentScalarAmp2622K04P090Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P090_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 200) 0) -
      (momentScalarAmp2622K04P090Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P090]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P090 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P090 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P090Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P090_replay] at h
  simpa only [momentPanelPhase_owner2622K04P090] using h

theorem momentScalarAmp2622K04P090_radius_le :
    (momentScalarAmp2622K04P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P090Expected]

def momentScalarGrow2622K04P090Input : RatPair2542 := (momentPanelGrowth2622K04P090 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P090Expected : RatState2542 :=
  ((((2362285474773539017958135898201658894444411495534440623602332100165223797182716911243596700656551 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2994552312423191847278261228868340349911275921117 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P090_replay :
    compactExp2620 momentScalarGrow2622K04P090Input 20 = momentScalarGrow2622K04P090Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P090_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P090Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P090Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P090 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P090]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P090 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P090 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P090Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P090Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P090_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P090] using h

theorem momentScalarGrow2622K04P090_radius_le :
    (momentScalarGrow2622K04P090Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P090Expected]

end ConnesWeilRH.Dev
