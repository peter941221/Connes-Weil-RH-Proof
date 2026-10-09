import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P172 : ℚ := ((-42913456700157330980007139962964000187496283219789527 : ℚ) / 466767085422557119501301843448762889402613455912960)

def momentPanelGrowth2622K00P172 : ℚ := ((38085924231320531649364587099399737009712999060436068397 : ℚ) / 7367126035476073782402086038468483849520533700660428800)

theorem momentPanelPhase_owner2622K00P172 :
    (momentPanelPhase2622K00P172 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P172 :
    (momentPanelGrowth2622K00P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P172Input : RatPair2542 := (momentPanelPhase2622K00P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P172Expected : RatState2542 :=
  ((((252113393630291815294622282894825988379434221731868979527 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629334542303 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P172_replay :
    compactExp2620 momentScalarAmp2622K00P172Input 20 = momentScalarAmp2622K00P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K00P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P172_replay] at h
  simpa only [momentPanelPhase_owner2622K00P172] using h

theorem momentScalarAmp2622K00P172_radius_le :
    (momentScalarAmp2622K00P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P172Expected]

def momentScalarGrow2622K00P172Input : RatPair2542 := (momentPanelGrowth2622K00P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P172Expected : RatState2542 :=
  ((((733679362646966694878206873757126624233027670939276946393889837919584833399944300355009688504483 : ℚ) / 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048), 0), ((119045695884444780233299181266962015603090573624745 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P172_replay :
    compactExp2620 momentScalarGrow2622K00P172Input 20 = momentScalarGrow2622K00P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P172] using h

theorem momentScalarGrow2622K00P172_radius_le :
    (momentScalarGrow2622K00P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622K00P172Expected]

end ConnesWeilRH.Dev
