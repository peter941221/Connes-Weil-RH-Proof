import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P106 : ℚ := ((-5409693385302703951593270974592506634787453769962458327 : ℚ) / 177714031906821135781948689143197776805724972436684800)

def momentPanelGrowth2622K00P106 : ℚ := ((9500819302699793819936465330369519877616457359208624797 : ℚ) / 71783724139358951716553372343459105617743045490166988800)

theorem momentPanelPhase_owner2622K00P106 :
    (momentPanelPhase2622K00P106 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P106 :
    (momentPanelGrowth2622K00P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P106Input : RatPair2542 := (momentPanelPhase2622K00P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P106Expected : RatState2542 :=
  ((((64335895709872545147961673725792225286456746092101527129295480283014949226934452669 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((40778902212225312147289944345168001 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P106_replay :
    compactExp2620 momentScalarAmp2622K00P106Input 20 = momentScalarAmp2622K00P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K00P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P106_replay] at h
  simpa only [momentPanelPhase_owner2622K00P106] using h

theorem momentScalarAmp2622K00P106_radius_le :
    (momentScalarAmp2622K00P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P106Expected]

def momentScalarGrow2622K00P106Input : RatPair2542 := (momentPanelGrowth2622K00P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P106Expected : RatState2542 :=
  ((((2438254081155978503196257569663138343957517940369671464952842829630788032122098065927701395617097 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3090853859352434194982972467490515668803850113559 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P106_replay :
    compactExp2620 momentScalarGrow2622K00P106Input 20 = momentScalarGrow2622K00P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P106] using h

theorem momentScalarGrow2622K00P106_radius_le :
    (momentScalarGrow2622K00P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P106Expected]

end ConnesWeilRH.Dev
