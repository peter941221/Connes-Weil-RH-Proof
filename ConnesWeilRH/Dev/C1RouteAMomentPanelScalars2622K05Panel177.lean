import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P177 : ℚ := ((-10284414839555298907436593012452569 : ℚ) / 81129638414606681695789005144064)

def momentPanelGrowth2622K05P177 : ℚ := ((69815623787022279872170232931959996803 : ℚ) / 6720576422169980994974921713621401600)

theorem momentPanelPhase_owner2622K05P177 :
    (momentPanelPhase2622K05P177 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P177 :
    (momentPanelGrowth2622K05P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P177Input : RatPair2542 := (momentPanelPhase2622K05P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P177Expected : RatState2542 :=
  ((((188873816101555553263854713025248315017183 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P177_replay :
    compactExp2620 momentScalarAmp2622K05P177Input 20 = momentScalarAmp2622K05P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K05P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P177_replay] at h
  simpa only [momentPanelPhase_owner2622K05P177] using h

theorem momentScalarAmp2622K05P177_radius_le :
    (momentScalarAmp2622K05P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P177Expected]

def momentScalarGrow2622K05P177Input : RatPair2542 := (momentPanelGrowth2622K05P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P177Expected : RatState2542 :=
  ((((69374004424854678054009505926279358487176552365037136496335524243289354537661085446985802645976896881 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((87941127104271496241917563318321224858799906605009727 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P177_replay :
    compactExp2620 momentScalarGrow2622K05P177Input 20 = momentScalarGrow2622K05P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P177] using h

theorem momentScalarGrow2622K05P177_radius_le :
    (momentScalarGrow2622K05P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P177Expected]

end ConnesWeilRH.Dev
