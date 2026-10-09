import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P150 : ℚ := ((-1770371986019498657678942042958326578832107220350507077 : ℚ) / 38606479188619132398674212159221063641098743080550400)

def momentPanelGrowth2622K00P150 : ℚ := ((28585898694420899826406526164037402552998335887203069037 : ℚ) / 30010901653462418145590876994158214814559724555259084800)

theorem momentPanelPhase_owner2622K00P150 :
    (momentPanelPhase2622K00P150 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (121 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P150 :
    (momentPanelGrowth2622K00P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P150Input : RatPair2542 := (momentPanelPhase2622K00P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P150Expected : RatState2542 :=
  ((((1622170626941325214001150779515049467973586743793863148367999412571460206065 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((32905385852237767221415883191 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P150_replay :
    compactExp2620 momentScalarAmp2622K00P150Input 20 = momentScalarAmp2622K00P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K00P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P150_replay] at h
  simpa only [momentPanelPhase_owner2622K00P150] using h

theorem momentScalarAmp2622K00P150_radius_le :
    (momentScalarAmp2622K00P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [momentScalarAmp2622K00P150Expected]

def momentScalarGrow2622K00P150Input : RatPair2542 := (momentPanelGrowth2622K00P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P150Expected : RatState2542 :=
  ((((5536962182394559276558660885512196884046946602810613553573526423426401449475284680994287909516057 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7018927058019368478917700337313761786826009242295 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P150_replay :
    compactExp2620 momentScalarGrow2622K00P150Input 20 = momentScalarGrow2622K00P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P150] using h

theorem momentScalarGrow2622K00P150_radius_le :
    (momentScalarGrow2622K00P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P150Expected]

end ConnesWeilRH.Dev
