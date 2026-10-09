import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P091 : ℚ := ((-85626890408120025085304927957977395251760860663779371 : ℚ) / 2853853123950202080170095710212737999954121012019200)

def momentPanelGrowth2622K01P091 : ℚ := ((1030338333428251207625581352432453615053261943067091 : ℚ) / 74276360568303434693073974479150554801711575413555200)

theorem momentPanelPhase_owner2622K01P091 :
    (momentPanelPhase2622K01P091 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P091 :
    (momentPanelGrowth2622K01P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P091Input : RatPair2542 := (momentPanelPhase2622K01P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P091Expected : RatState2542 :=
  ((((99543990995223046768786747436233465270368427905362257275949135583994749101185117957 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((126190610702461837214351538026168087 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P091_replay :
    compactExp2620 momentScalarAmp2622K01P091Input 20 = momentScalarAmp2622K01P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K01P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P091_replay] at h
  simpa only [momentPanelPhase_owner2622K01P091] using h

theorem momentScalarAmp2622K01P091_radius_le :
    (momentScalarAmp2622K01P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P091Expected]

def momentScalarGrow2622K01P091Input : RatPair2542 := (momentPanelGrowth2622K01P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P091Expected : RatState2542 :=
  ((((2165823237653527919718785222287048330769166186526950365601001341332984479846977108518726162266817 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2745507090879234920095484978559112531912907873689 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P091_replay :
    compactExp2620 momentScalarGrow2622K01P091Input 20 = momentScalarGrow2622K01P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P091] using h

theorem momentScalarGrow2622K01P091_radius_le :
    (momentScalarGrow2622K01P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P091Expected]

end ConnesWeilRH.Dev
