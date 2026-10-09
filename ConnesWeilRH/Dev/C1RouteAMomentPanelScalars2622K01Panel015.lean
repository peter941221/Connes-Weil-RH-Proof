import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P015 : ℚ := ((-28603689034998495084546319796271186854117641398708641 : ℚ) / 423393028041222998715940532837192732207941786009600)

def momentPanelGrowth2622K01P015 : ℚ := ((4113728975488115997639567394041863252740741774497 : ℚ) / 1748378423564800854296400312575631542068864614400)

theorem momentPanelPhase_owner2622K01P015 :
    (momentPanelPhase2622K01P015 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-149 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P015, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P015 :
    (momentPanelGrowth2622K01P015 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P015, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P015Input : RatPair2542 := (momentPanelPhase2622K01P015 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P015Expected : RatState2542 :=
  ((((9759476201725435443012999429640665581450910636533146277865892100417 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302233001454030519880033 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P015_replay :
    compactExp2620 momentScalarAmp2622K01P015Input 20 = momentScalarAmp2622K01P015Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P015_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-149 / 200) 0) -
      (momentScalarAmp2622K01P015Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P015]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P015 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P015 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P015Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P015_replay] at h
  simpa only [momentPanelPhase_owner2622K01P015] using h

theorem momentScalarAmp2622K01P015_radius_le :
    (momentScalarAmp2622K01P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P015Expected]

def momentScalarGrow2622K01P015Input : RatPair2542 := (momentPanelGrowth2622K01P015 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P015Expected : RatState2542 :=
  ((((5615423334216274060085536102822831148455312296711780562169375513617569601542911343392277181750135 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((28473515149294143738542995346339526503442422345099 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P015_replay :
    compactExp2620 momentScalarGrow2622K01P015Input 20 = momentScalarGrow2622K01P015Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P015_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P015Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P015]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P015 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P015 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P015Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P015_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P015] using h

theorem momentScalarGrow2622K01P015_radius_le :
    (momentScalarGrow2622K01P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P015Expected]

end ConnesWeilRH.Dev
