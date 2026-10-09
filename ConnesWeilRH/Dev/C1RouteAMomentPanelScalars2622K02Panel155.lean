import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P155 : ℚ := ((-108360325051576389595427456739118573005727671936600263 : ℚ) / 2173127336914094514899346217083801294656370009702400)

def momentPanelGrowth2622K02P155 : ℚ := ((364861281859438924865780747541202336107107252430052359 : ℚ) / 284153740360984235235644376058235830642227429140070400)

theorem momentPanelPhase_owner2622K02P155 :
    (momentPanelPhase2622K02P155 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P155 :
    (momentPanelGrowth2622K02P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P155Input : RatPair2542 := (momentPanelPhase2622K02P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P155Expected : RatState2542 :=
  ((((472104115659416182746446679477514736285004408378955712516487116878613682147 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((300454688546865851123704081 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P155_replay :
    compactExp2620 momentScalarAmp2622K02P155Input 20 = momentScalarAmp2622K02P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K02P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P155_replay] at h
  simpa only [momentPanelPhase_owner2622K02P155] using h

theorem momentScalarAmp2622K02P155_radius_le :
    (momentScalarAmp2622K02P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P155Expected]

def momentScalarGrow2622K02P155Input : RatPair2542 := (momentPanelGrowth2622K02P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P155Expected : RatState2542 :=
  ((((7713380750690674279019094770806702649467926998052938860690557609915671762217083135623853847863367 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((9777859764972459394688934644721221378791437678923 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P155_replay :
    compactExp2620 momentScalarGrow2622K02P155Input 20 = momentScalarGrow2622K02P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P155] using h

theorem momentScalarGrow2622K02P155_radius_le :
    (momentScalarGrow2622K02P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P155Expected]

end ConnesWeilRH.Dev
