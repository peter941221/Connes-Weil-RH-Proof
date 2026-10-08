import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P091 : ℚ := ((-340917895123498862908750018436601275941894465741580229 : ℚ) / 11415412495800808320680382840850951999816484048076800)

def momentPanelGrowth2622K04P091 : ℚ := ((31703862004425961765286728909944475092634303593764509 : ℚ) / 297105442273213738772295897916602219206846301654220800)

theorem momentPanelPhase_owner2622K04P091 :
    (momentPanelPhase2622K04P091 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P091 :
    (momentPanelGrowth2622K04P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P091Input : RatPair2542 := (momentPanelPhase2622K04P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P091Expected : RatState2542 :=
  ((((57208852274371512328138123389725236474840409143175696991884347767780568706737716137 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((290091605737555577975215701336399419 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P091_replay :
    compactExp2620 momentScalarAmp2622K04P091Input 20 = momentScalarAmp2622K04P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K04P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P091_replay] at h
  simpa only [momentPanelPhase_owner2622K04P091] using h

theorem momentScalarAmp2622K04P091_radius_le :
    (momentScalarAmp2622K04P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P091Expected]

def momentScalarGrow2622K04P091Input : RatPair2542 := (momentPanelGrowth2622K04P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P091Expected : RatState2542 :=
  ((((2376521769897870870963690624227475737169260293786174126748847093147787660077197148774828788646031 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1506299470743538042532771281806731034433210299765 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P091_replay :
    compactExp2620 momentScalarGrow2622K04P091Input 20 = momentScalarGrow2622K04P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P091] using h

theorem momentScalarGrow2622K04P091_radius_le :
    (momentScalarGrow2622K04P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P091Expected]

end ConnesWeilRH.Dev
