import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P128 : ℚ := ((-109076972740067126948880277970178256200555535894868969 : ℚ) / 3241850409212317273835790751007583252779770681753600)

def momentPanelGrowth2622K02P128 : ℚ := ((3759274219056062305230027592948256657519268563183903439 : ℚ) / 10260974778794205705723089990574508106731994783049318400)

theorem momentPanelPhase_owner2622K02P128 :
    (momentPanelPhase2622K02P128 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P128 :
    (momentPanelGrowth2622K02P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P128Input : RatPair2542 := (momentPanelPhase2622K02P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P128Expected : RatState2542 :=
  ((((5213174162423324225276532397359403129051727343728831044058224739719156329247939799 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((826086926715561935202437755045807 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P128_replay :
    compactExp2620 momentScalarAmp2622K02P128Input 20 = momentScalarAmp2622K02P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K02P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P128_replay] at h
  simpa only [momentPanelPhase_owner2622K02P128] using h

theorem momentScalarAmp2622K02P128_radius_le :
    (momentScalarAmp2622K02P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P128Expected]

def momentScalarGrow2622K02P128Input : RatPair2542 := (momentPanelGrowth2622K02P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P128Expected : RatState2542 :=
  ((((770281442668420031056151218188051696848531265331937240067741891030414098933673454173890298617179 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((15256990499661652479670165052895213613708734235 : ℚ) / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896))

theorem momentScalarGrow2622K02P128_replay :
    compactExp2620 momentScalarGrow2622K02P128Input 20 = momentScalarGrow2622K02P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P128] using h

theorem momentScalarGrow2622K02P128_radius_le :
    (momentScalarGrow2622K02P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P128Expected]

end ConnesWeilRH.Dev
