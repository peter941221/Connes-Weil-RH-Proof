import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P127 : ℚ := ((-3938477996305514285914978967553136906493191737537 : ℚ) / 125597796958124469533129165311555572001681702912)

def momentPanelGrowth2622K04P127 : ℚ := ((88407561503622491155409967313706618181940730312777389 : ℚ) / 217670544687970835632115934000921117896328155548876800)

theorem momentPanelPhase_owner2622K04P127 :
    (momentPanelPhase2622K04P127 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P127 :
    (momentPanelGrowth2622K04P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P127Input : RatPair2542 := (momentPanelPhase2622K04P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P127Expected : RatState2542 :=
  ((((51410700800524494319209507877832732569654899267422735256685099789406372580903302433 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((65172754704478388624907079962711225 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P127_replay :
    compactExp2620 momentScalarAmp2622K04P127Input 20 = momentScalarAmp2622K04P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K04P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P127_replay] at h
  simpa only [momentPanelPhase_owner2622K04P127] using h

theorem momentScalarAmp2622K04P127_radius_le :
    (momentScalarAmp2622K04P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P127Expected]

def momentScalarGrow2622K04P127Input : RatPair2542 := (momentPanelGrowth2622K04P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P127Expected : RatState2542 :=
  ((((3206185551323647079542004358099496279466472501792279354883977691384286268015568288130076410302815 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2032160732156514430796815442727363760330119599893 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P127_replay :
    compactExp2620 momentScalarGrow2622K04P127Input 20 = momentScalarGrow2622K04P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P127] using h

theorem momentScalarGrow2622K04P127_radius_le :
    (momentScalarGrow2622K04P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P127Expected]

end ConnesWeilRH.Dev
