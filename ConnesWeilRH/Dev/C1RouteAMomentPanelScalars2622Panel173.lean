import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P173 : ℚ := ((-1789632188336643252986235792897736362789541388742177691 : ℚ) / 18437756593452672127463361467736357969846873987481600)

def momentPanelGrowth2622P173 : ℚ := ((7053959216577542495684012256583958444315285445133159 : ℚ) / 1208022447106324443327733244542052683434356742553600)

theorem momentPanelPhase_owner2622P173 :
    (momentPanelPhase2622P173 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (167 / 200) 0 := by
  norm_num [momentPanelPhase2622P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P173 :
    (momentPanelGrowth2622P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P173Input : RatPair2542 := (momentPanelPhase2622P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P173Expected : RatState2542 :=
  ((((1497889215517810613560684239419646094026326268096535003 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629175657689 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P173_replay :
    compactExp2620 momentScalarAmp2622P173Input 20 = momentScalarAmp2622P173Expected := by
  decide +kernel

theorem momentScalarAmp2622P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P173]
  have h := compactExp_real_error2620 momentPanelPhase2622P173 20 hsmall
  change |Real.exp (momentPanelPhase2622P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P173_replay] at h
  simpa only [momentPanelPhase_owner2622P173] using h

theorem momentScalarAmp2622P173_radius_le :
    (momentScalarAmp2622P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P173Expected]

def momentScalarGrow2622P173Input : RatPair2542 := (momentPanelGrowth2622P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P173Expected : RatState2542 :=
  ((((733766280336612522098001877967198402548742815089110478297209499426757904829490643622435760751304115 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((465077042941155328747898304488575229884251319670969 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P173_replay :
    compactExp2620 momentScalarGrow2622P173Input 20 = momentScalarGrow2622P173Expected := by
  decide +kernel

theorem momentScalarGrow2622P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P173_replay] at h
  simpa only [momentPanelGrowth_owner2622P173] using h

theorem momentScalarGrow2622P173_radius_le :
    (momentScalarGrow2622P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622P173Expected]

end ConnesWeilRH.Dev
