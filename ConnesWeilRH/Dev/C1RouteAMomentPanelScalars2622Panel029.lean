import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P029 : ℚ := ((-1883382107307758637830270038832380970307724137089492923 : ℚ) / 38606479188619132398674212159221063641098743080550400)

def momentPanelGrowth2622P029 : ℚ := ((28585898694420899826406526164037402552998335887203069037 : ℚ) / 30010901653462418145590876994158214814559724555259084800)

theorem momentPanelPhase_owner2622P029 :
    (momentPanelPhase2622P029 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-121 / 200) 0 := by
  norm_num [momentPanelPhase2622P029, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P029 :
    (momentPanelGrowth2622P029 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P029, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P029Input : RatPair2542 := (momentPanelPhase2622P029 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P029Expected : RatState2542 :=
  ((((1389747210705712999750714598204220066367464493338708734059916434473838767887 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1764213701581545536740504563 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P029_replay :
    compactExp2620 momentScalarAmp2622P029Input 20 = momentScalarAmp2622P029Expected := by
  decide +kernel

theorem momentScalarAmp2622P029_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-121 / 200) 0) -
      (momentScalarAmp2622P029Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P029]
  have h := compactExp_real_error2620 momentPanelPhase2622P029 20 hsmall
  change |Real.exp (momentPanelPhase2622P029 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P029Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P029_replay] at h
  simpa only [momentPanelPhase_owner2622P029] using h

theorem momentScalarAmp2622P029_radius_le :
    (momentScalarAmp2622P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [momentScalarAmp2622P029Expected]

def momentScalarGrow2622P029Input : RatPair2542 := (momentPanelGrowth2622P029 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P029Expected : RatState2542 :=
  ((((5536962182394559276558660885512196884046946602810613553573526423426401449475284680994287909516057 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7018927058019368478917700337313761786826009242295 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P029_replay :
    compactExp2620 momentScalarGrow2622P029Input 20 = momentScalarGrow2622P029Expected := by
  decide +kernel

theorem momentScalarGrow2622P029_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P029Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P029]
  have h := compactExp_real_error2620 momentPanelGrowth2622P029 20 hsmall
  change |Real.exp (momentPanelGrowth2622P029 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P029Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P029_replay] at h
  simpa only [momentPanelGrowth_owner2622P029] using h

theorem momentScalarGrow2622P029_radius_le :
    (momentScalarGrow2622P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P029Expected]

end ConnesWeilRH.Dev
