import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P035 : ℚ := ((-127988497858908064402984890839651231836703015713359239 : ℚ) / 2675518524746592393031862878330023582663096821350400)

def momentPanelGrowth2622K04P035 : ℚ := ((2862654738596902568821888512060412749738440090480069 : ℚ) / 3703279588264154103381934604930605030372312665292800)

theorem momentPanelPhase_owner2622K04P035 :
    (momentPanelPhase2622K04P035 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P035 :
    (momentPanelGrowth2622K04P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P035Input : RatPair2542 := (momentPanelPhase2622K04P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P035Expected : RatState2542 :=
  ((((3583432476984317062998478339996068647720816483034203761009945889803113187935 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4545165421097971307861069977 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P035_replay :
    compactExp2620 momentScalarAmp2622K04P035Input 20 = momentScalarAmp2622K04P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K04P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P035_replay] at h
  simpa only [momentPanelPhase_owner2622K04P035] using h

theorem momentScalarAmp2622K04P035_radius_le :
    (momentScalarAmp2622K04P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P035Expected]

def momentScalarGrow2622K04P035Input : RatPair2542 := (momentPanelGrowth2622K04P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P035Expected : RatState2542 :=
  ((((1156779426926424238328946374536385541143465486272516333110097624962481651714939556210252255781481 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2932782107715920081117611580449092802571422028023 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P035_replay :
    compactExp2620 momentScalarGrow2622K04P035Input 20 = momentScalarGrow2622K04P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P035] using h

theorem momentScalarGrow2622K04P035_radius_le :
    (momentScalarGrow2622K04P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P035Expected]

end ConnesWeilRH.Dev
