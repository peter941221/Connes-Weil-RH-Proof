import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P036 : ℚ := ((-1883133837347819997848768010595812799764676961103352249 : ℚ) / 43465972132744384601701464228002704681454718785945600)

def momentPanelGrowth2622K00P036 : ℚ := ((4797554460597819120597294014165031217003692229794499711 : ℚ) / 7162365088893397624490130406889830360082301126600294400)

theorem momentPanelPhase_owner2622K00P036 :
    (momentPanelPhase2622K00P036 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-107 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P036 :
    (momentPanelGrowth2622K00P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P036Input : RatPair2542 := (momentPanelPhase2622K00P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P036Expected : RatState2542 :=
  ((((326650998416802673935634735918850632877863393539957654696143520730887426440243 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((51762357631391336752069931951 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K00P036_replay :
    compactExp2620 momentScalarAmp2622K00P036Input 20 = momentScalarAmp2622K00P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K00P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P036_replay] at h
  simpa only [momentPanelPhase_owner2622K00P036] using h

theorem momentScalarAmp2622K00P036_radius_le :
    (momentScalarAmp2622K00P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarAmp2622K00P036Expected]

def momentScalarGrow2622K00P036Input : RatPair2542 := (momentPanelGrowth2622K00P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P036Expected : RatState2542 :=
  ((((4173508712876383870611694848327423274229100387621120395569986370032605758020983899614098748902387 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5290547445343304106789188937369451588119360813167 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P036_replay :
    compactExp2620 momentScalarGrow2622K00P036Input 20 = momentScalarGrow2622K00P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P036] using h

theorem momentScalarGrow2622K00P036_radius_le :
    (momentScalarGrow2622K00P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P036Expected]

end ConnesWeilRH.Dev
