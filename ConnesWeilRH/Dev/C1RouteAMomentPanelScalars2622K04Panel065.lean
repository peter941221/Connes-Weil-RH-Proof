import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P065 : ℚ := ((-122480200609842633076548568968773155151263594956465659 : ℚ) / 3577539066536759037860699611022104508856992687718400)

def momentPanelGrowth2622K04P065 : ℚ := ((568114916463268669867319176631667187856985813649 : ℚ) / 2140871539058939821587428954174242704574119936000)

theorem momentPanelPhase_owner2622K04P065 :
    (momentPanelPhase2622K04P065 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-49 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P065, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P065 :
    (momentPanelGrowth2622K04P065 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P065, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P065Input : RatPair2542 := (momentPanelPhase2622K04P065 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P065Expected : RatState2542 :=
  ((((90363817907119828092127045850772561137900096267328005327462272456503395699821647 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((3665711621792886476793720330345703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P065_replay :
    compactExp2620 momentScalarAmp2622K04P065Input 20 = momentScalarAmp2622K04P065Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P065_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-49 / 200) 0) -
      (momentScalarAmp2622K04P065Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P065]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P065 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P065 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P065Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P065_replay] at h
  simpa only [momentPanelPhase_owner2622K04P065] using h

theorem momentScalarAmp2622K04P065_radius_le :
    (momentScalarAmp2622K04P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P065Expected]

def momentScalarGrow2622K04P065Input : RatPair2542 := (momentPanelGrowth2622K04P065 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P065Expected : RatState2542 :=
  ((((2785131357738390842300465890533303395309130455885847281661781758773582764856379931001420332242793 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3530572543859130486216190768285303398065110940537 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P065_replay :
    compactExp2620 momentScalarGrow2622K04P065Input 20 = momentScalarGrow2622K04P065Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P065_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P065Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P065]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P065 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P065 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P065Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P065_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P065] using h

theorem momentScalarGrow2622K04P065_radius_le :
    (momentScalarGrow2622K04P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P065Expected]

end ConnesWeilRH.Dev
