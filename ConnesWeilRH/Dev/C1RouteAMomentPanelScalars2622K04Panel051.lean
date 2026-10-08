import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P051 : ℚ := ((-125999380006548881506952647091569117713812627839897703 : ℚ) / 3241850409212317273835790751007583252779770681753600)

def momentPanelGrowth2622K04P051 : ℚ := ((4311468987215864000183287747009592149042175059280341407 : ℚ) / 10260974778794205705723089990574508106731994783049318400)

theorem momentPanelPhase_owner2622K04P051 :
    (momentPanelPhase2622K04P051 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-77 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P051, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P051 :
    (momentPanelGrowth2622K04P051 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P051, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P051Input : RatPair2542 := (momentPanelPhase2622K04P051 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P051Expected : RatState2542 :=
  ((((28189799522865127952853234890162041690013792474113805852029405215989311182213359 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((35736143273970980684166145062323 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P051_replay :
    compactExp2620 momentScalarAmp2622K04P051Input 20 = momentScalarAmp2622K04P051Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P051_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-77 / 200) 0) -
      (momentScalarAmp2622K04P051Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P051]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P051 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P051 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P051Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P051_replay] at h
  simpa only [momentPanelPhase_owner2622K04P051] using h

theorem momentScalarAmp2622K04P051_radius_le :
    (momentScalarAmp2622K04P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P051Expected]

def momentScalarGrow2622K04P051Input : RatPair2542 := (momentPanelGrowth2622K04P051 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P051Expected : RatState2542 :=
  ((((3251479359006720569742036810099188559485038685465306375160264293550981254048543034678636572297155 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4121738109427640175222522560272647176521006859921 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P051_replay :
    compactExp2620 momentScalarGrow2622K04P051Input 20 = momentScalarGrow2622K04P051Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P051_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P051Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P051]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P051 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P051 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P051Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P051_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P051] using h

theorem momentScalarGrow2622K04P051_radius_le :
    (momentScalarGrow2622K04P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P051Expected]

end ConnesWeilRH.Dev
