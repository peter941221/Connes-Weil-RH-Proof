import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P158 : ℚ := ((-28480535821562875767261102459361669624074579421829123 : ℚ) / 505031596064003903912474490289703854009034892902400)

def momentPanelGrowth2622K01P158 : ℚ := ((1479024982555872860829572048796631999614663659487300033 : ℚ) / 979346002966782456913809576402064909930218722531737600)

theorem momentPanelPhase_owner2622K01P158 :
    (momentPanelPhase2622K01P158 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (137 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P158 :
    (momentPanelGrowth2622K01P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P158Input : RatPair2542 := (momentPanelPhase2622K01P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P158Expected : RatState2542 :=
  ((((172234980660985183392511129846134453809268641604272310062515540143616451 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1645616857939918157239349 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P158_replay :
    compactExp2620 momentScalarAmp2622K01P158Input 20 = momentScalarAmp2622K01P158Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622K01P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P158]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P158 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P158_replay] at h
  simpa only [momentPanelPhase_owner2622K01P158] using h

theorem momentScalarAmp2622K01P158_radius_le :
    (momentScalarAmp2622K01P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P158Expected]

def momentScalarGrow2622K01P158Input : RatPair2542 := (momentPanelGrowth2622K01P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P158Expected : RatState2542 :=
  ((((9671136700672359492970621822796626332255715056227824586165237192059900514806073091839564933675199 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12259604586525031867485708576834603952227704958107 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P158_replay :
    compactExp2620 momentScalarGrow2622K01P158Input 20 = momentScalarGrow2622K01P158Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P158_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P158] using h

theorem momentScalarGrow2622K01P158_radius_le :
    (momentScalarGrow2622K01P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P158Expected]

end ConnesWeilRH.Dev
