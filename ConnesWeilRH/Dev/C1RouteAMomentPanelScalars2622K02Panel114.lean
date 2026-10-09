import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P114 : ℚ := ((-110596302718308290547437592035133976499574545083905557 : ℚ) / 3577539066536759037860699611022104508856992687718400)

def momentPanelGrowth2622K02P114 : ℚ := ((452903828953950185246463397716869767424103800929 : ℚ) / 2140871539058939821587428954174242704574119936000)

theorem momentPanelPhase_owner2622K02P114 :
    (momentPanelPhase2622K02P114 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (49 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P114, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P114 :
    (momentPanelGrowth2622K02P114 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P114, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P114Input : RatPair2542 := (momentPanelPhase2622K02P114 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P114Expected : RatState2542 :=
  ((((80128577778545522697375495863198051254074274767355231947643469953478791851436048831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6348627149621007034904131523538843 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K02P114_replay :
    compactExp2620 momentScalarAmp2622K02P114Input 20 = momentScalarAmp2622K02P114Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P114_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (49 / 200) 0) -
      (momentScalarAmp2622K02P114Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P114]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P114 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P114 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P114Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P114_replay] at h
  simpa only [momentPanelPhase_owner2622K02P114] using h

theorem momentScalarAmp2622K02P114_radius_le :
    (momentScalarAmp2622K02P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P114Expected]

def momentScalarGrow2622K02P114Input : RatPair2542 := (momentPanelGrowth2622K02P114 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P114Expected : RatState2542 :=
  ((((2639210972466577967965074412799662703601095684329446692385712704368915288215885880792698273165285 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((418199587299873716852382971387045974248332445945 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P114_replay :
    compactExp2620 momentScalarGrow2622K02P114Input 20 = momentScalarGrow2622K02P114Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P114_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P114Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P114]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P114 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P114 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P114Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P114_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P114] using h

theorem momentScalarGrow2622K02P114_radius_le :
    (momentScalarGrow2622K02P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P114Expected]

end ConnesWeilRH.Dev
