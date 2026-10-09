import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P032 : ℚ := ((-228905179810179031918592692223068242668559480757603 : ℚ) / 5095274262960276775378080910934697636886405447680)

def momentPanelGrowth2622K01P032 : ℚ := ((25929819412822500531190703481629560405138995485389571 : ℚ) / 32734889224403766394991503052353549362155352175411200)

theorem momentPanelPhase_owner2622K01P032 :
    (momentPanelPhase2622K01P032 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P032, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P032 :
    (momentPanelGrowth2622K01P032 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P032, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P032Input : RatPair2542 := (momentPanelPhase2622K01P032 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P032Expected : RatState2542 :=
  ((((65905311243443856964650075138340684106590435527293716256631853664628406222701 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((83550904666902086922235451319 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P032_replay :
    compactExp2620 momentScalarAmp2622K01P032Input 20 = momentScalarAmp2622K01P032Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P032_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 40) 0) -
      (momentScalarAmp2622K01P032Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P032]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P032 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P032 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P032Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P032_replay] at h
  simpa only [momentPanelPhase_owner2622K01P032] using h

theorem momentScalarAmp2622K01P032_radius_le :
    (momentScalarAmp2622K01P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P032Expected]

def momentScalarGrow2622K01P032Input : RatPair2542 := (momentPanelGrowth2622K01P032 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P032Expected : RatState2542 :=
  ((((589549260995255972445500005170755055442512632809382798970923440812786006011917502858855062588001 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2989367640028858143560185634667146361771748530259 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P032_replay :
    compactExp2620 momentScalarGrow2622K01P032Input 20 = momentScalarGrow2622K01P032Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P032_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P032Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P032]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P032 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P032 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P032Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P032_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P032] using h

theorem momentScalarGrow2622K01P032_radius_le :
    (momentScalarGrow2622K01P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P032Expected]

end ConnesWeilRH.Dev
