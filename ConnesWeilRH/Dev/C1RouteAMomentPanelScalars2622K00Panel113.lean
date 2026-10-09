import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P113 : ℚ := ((-1794168888183141053449285761475168086197426144412376211 : ℚ) / 57532925392054325189411930742896928745643069512089600)

def momentPanelGrowth2622K00P113 : ℚ := ((147617860383561516358589114611038962133029603878715791 : ℚ) / 792227514881990892634594602891821283534462146471526400)

theorem momentPanelPhase_owner2622K00P113 :
    (momentPanelPhase2622K00P113 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (47 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P113, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P113 :
    (momentPanelGrowth2622K00P113 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P113, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P113Input : RatPair2542 := (momentPanelPhase2622K00P113 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P113Expected : RatState2542 :=
  ((((7638365036934326834792577587338433945603191843582219083654357863692208620070190393 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9683065998204646048665139154543787 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K00P113_replay :
    compactExp2620 momentScalarAmp2622K00P113Input 20 = momentScalarAmp2622K00P113Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P113_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (47 / 200) 0) -
      (momentScalarAmp2622K00P113Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P113]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P113 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P113 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P113Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P113_replay] at h
  simpa only [momentPanelPhase_owner2622K00P113] using h

theorem momentScalarAmp2622K00P113_radius_le :
    (momentScalarAmp2622K00P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P113Expected]

def momentScalarGrow2622K00P113Input : RatPair2542 := (momentPanelGrowth2622K00P113 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P113Expected : RatState2542 :=
  ((((643371572048607488446821241679821631928181777770603009920150153180537584988356927977143309935031 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((815570214549808441831360930745588013219952652015 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P113_replay :
    compactExp2620 momentScalarGrow2622K00P113Input 20 = momentScalarGrow2622K00P113Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P113_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P113Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P113]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P113 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P113 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P113Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P113_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P113] using h

theorem momentScalarGrow2622K00P113_radius_le :
    (momentScalarGrow2622K00P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P113Expected]

end ConnesWeilRH.Dev
