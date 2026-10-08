import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P060 : ℚ := ((-123887077629657180720384159937855205998266071539341089 : ℚ) / 3474777232661929926424503021221740859037434930790400)

def momentPanelGrowth2622K04P060 : ℚ := ((368830308590274517841164246284639195295628070702087 : ℚ) / 1181903814329805377504366611301126922438552479334400)

theorem momentPanelPhase_owner2622K04P060 :
    (momentPanelPhase2622K04P060 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-59 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P060, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P060 :
    (momentPanelGrowth2622K04P060 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P060, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P060Input : RatPair2542 := (momentPanelPhase2622K04P060 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P060Expected : RatState2542 :=
  ((((700796368696697053342958185428773453795504372573096805896801956274380433239429603 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((888395146161048841770862839943281 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P060_replay :
    compactExp2620 momentScalarAmp2622K04P060Input 20 = momentScalarAmp2622K04P060Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P060_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-59 / 200) 0) -
      (momentScalarAmp2622K04P060Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P060]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P060 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P060 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P060Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P060_replay] at h
  simpa only [momentPanelPhase_owner2622K04P060] using h

theorem momentScalarAmp2622K04P060_radius_le :
    (momentScalarAmp2622K04P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P060Expected]

def momentScalarGrow2622K04P060Input : RatPair2542 := (momentPanelGrowth2622K04P060 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P060Expected : RatState2542 :=
  ((((729569286956979536530367333959459208746349844830031740845339479258703870098174205293226736975507 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1849677338559397045831062000883648816866817734453 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P060_replay :
    compactExp2620 momentScalarGrow2622K04P060Input 20 = momentScalarGrow2622K04P060Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P060_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P060Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P060]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P060 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P060 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P060Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P060_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P060] using h

theorem momentScalarGrow2622K04P060_radius_le :
    (momentScalarGrow2622K04P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P060Expected]

end ConnesWeilRH.Dev
