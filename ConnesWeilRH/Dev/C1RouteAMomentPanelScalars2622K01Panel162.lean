import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P162 : ℚ := ((-227872151494760530961437371530808472100524931344999 : ℚ) / 3610936662546078499077463502707222695048348958720)

def momentPanelGrowth2622K01P162 : ℚ := ((521428618127222240853102812544632368053394411581511931 : ℚ) / 259500284384604790177175152736397685116055284036403200)

theorem momentPanelPhase_owner2622K01P162 :
    (momentPanelPhase2622K01P162 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P162 :
    (momentPanelGrowth2622K01P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P162Input : RatPair2542 := (momentPanelPhase2622K01P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P162Expected : RatState2542 :=
  ((((104682732483687457574674763537502188540911062395558672154843490920629 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1209456656075538481705897 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P162_replay :
    compactExp2620 momentScalarAmp2622K01P162Input 20 = momentScalarAmp2622K01P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K01P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P162_replay] at h
  simpa only [momentPanelPhase_owner2622K01P162] using h

theorem momentScalarAmp2622K01P162_radius_le :
    (momentScalarAmp2622K01P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P162Expected]

def momentScalarGrow2622K01P162Input : RatPair2542 := (momentPanelGrowth2622K01P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P162Expected : RatState2542 :=
  ((((15931296157404194357444656989176855277785582518866815047073829225877674174794696189013839958505167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20195278436667168459032523275245510665728486020039 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P162_replay :
    compactExp2620 momentScalarGrow2622K01P162Input 20 = momentScalarGrow2622K01P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P162] using h

theorem momentScalarGrow2622K01P162_radius_le :
    (momentScalarGrow2622K01P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P162Expected]

end ConnesWeilRH.Dev
