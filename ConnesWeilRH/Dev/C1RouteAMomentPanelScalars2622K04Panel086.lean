import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P086 : ℚ := ((-115439760357490262641553164370705116702787314362108413 : ℚ) / 3801331504753053547210638851031785346241807358361600)

def momentPanelGrowth2622K04P086 : ℚ := ((8594841059647556315626729323748412676128210513189 : ℚ) / 72361458020192165969655098651089403414605253836800)

theorem momentPanelPhase_owner2622K04P086 :
    (momentPanelPhase2622K04P086 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P086, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P086 :
    (momentPanelGrowth2622K04P086 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P086, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P086Input : RatPair2542 := (momentPanelPhase2622K04P086 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P086Expected : RatState2542 :=
  ((((138305063812841245109017426533857277461267314638317158793008392052747480419595705325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((175327574820278852937083046335072213 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P086_replay :
    compactExp2620 momentScalarAmp2622K04P086Input 20 = momentScalarAmp2622K04P086Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P086_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 200) 0) -
      (momentScalarAmp2622K04P086Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P086]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P086 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P086 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P086Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P086_replay] at h
  simpa only [momentPanelPhase_owner2622K04P086] using h

theorem momentScalarAmp2622K04P086_radius_le :
    (momentScalarAmp2622K04P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P086Expected]

def momentScalarGrow2622K04P086Input : RatPair2542 := (momentPanelGrowth2622K04P086 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P086Expected : RatState2542 :=
  ((((300671736663767928724172438352892117937212015516695290396326461231617089014545236598205695662201 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3049173314235528019893317605921970275276553706925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P086_replay :
    compactExp2620 momentScalarGrow2622K04P086Input 20 = momentScalarGrow2622K04P086Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P086_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P086Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P086]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P086 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P086 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P086Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P086_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P086] using h

theorem momentScalarGrow2622K04P086_radius_le :
    (momentScalarGrow2622K04P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P086Expected]

end ConnesWeilRH.Dev
