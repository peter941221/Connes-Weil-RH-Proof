import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P093 : ℚ := ((-112919870475463318327772590741214105118452145477891587 : ℚ) / 3801331504753053547210638851031785346241807358361600)

def momentPanelGrowth2622K04P093 : ℚ := ((8594841059647556315626729323748412676128210513189 : ℚ) / 72361458020192165969655098651089403414605253836800)

theorem momentPanelPhase_owner2622K04P093 :
    (momentPanelPhase2622K04P093 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P093 :
    (momentPanelGrowth2622K04P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P093Input : RatPair2542 := (momentPanelPhase2622K04P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P093Expected : RatState2542 :=
  ((((67091954360467271656679812932811207603991477187788838019403412914597929082057228569 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((21262891406763392706664226953846401 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K04P093_replay :
    compactExp2620 momentScalarAmp2622K04P093Input 20 = momentScalarAmp2622K04P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K04P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P093_replay] at h
  simpa only [momentPanelPhase_owner2622K04P093] using h

theorem momentScalarAmp2622K04P093_radius_le :
    (momentScalarAmp2622K04P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P093Expected]

def momentScalarGrow2622K04P093Input : RatPair2542 := (momentPanelGrowth2622K04P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P093Expected : RatState2542 :=
  ((((300671736663767928724172438352892117937212015516695290396326461231617089014545236598205695662201 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3049173314235528019893317605921970275276553706925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P093_replay :
    compactExp2620 momentScalarGrow2622K04P093Input 20 = momentScalarGrow2622K04P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P093] using h

theorem momentScalarGrow2622K04P093_radius_le :
    (momentScalarGrow2622K04P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P093Expected]

end ConnesWeilRH.Dev
