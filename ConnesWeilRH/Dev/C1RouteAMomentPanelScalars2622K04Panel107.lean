import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P107 : ℚ := ((-864524238244785330476966737259013787896909393270787 : ℚ) / 29515482285159250340285353848215559420395200184320)

def momentPanelGrowth2622K04P107 : ℚ := ((175428725463272757196818437116270497422394709981630647 : ℚ) / 835162693597817930756530490567785720974696121788006400)

theorem momentPanelPhase_owner2622K04P107 :
    (momentPanelPhase2622K04P107 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P107 :
    (momentPanelGrowth2622K04P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P107Input : RatPair2542 := (momentPanelPhase2622K04P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P107Expected : RatState2542 :=
  ((((203166133806900118554653350863463616694205692623769256436172080244864156142059802679 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((515101731395373182767664054550908237 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P107_replay :
    compactExp2620 momentScalarAmp2622K04P107Input 20 = momentScalarAmp2622K04P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K04P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P107_replay] at h
  simpa only [momentPanelPhase_owner2622K04P107] using h

theorem momentScalarAmp2622K04P107_radius_le :
    (momentScalarAmp2622K04P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P107Expected]

def momentScalarGrow2622K04P107Input : RatPair2542 := (momentPanelGrowth2622K04P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P107Expected : RatState2542 :=
  ((((2635260942224749951718855839787302006861932450706480613333844225023042564117331132206753651543873 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1670294722986976399155478384464717758638233783611 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P107_replay :
    compactExp2620 momentScalarGrow2622K04P107Input 20 = momentScalarGrow2622K04P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P107] using h

theorem momentScalarGrow2622K04P107_radius_le :
    (momentScalarGrow2622K04P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P107Expected]

end ConnesWeilRH.Dev
