import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P019 : ℚ := ((-5637348320383581801760778994716238952756214514306006909 : ℚ) / 91887348254563861910437297341934056476430333850419200)

def momentPanelGrowth2622P019 : ℚ := ((32879921432061771203395909743818429568947773049692985917 : ℚ) / 18719157315739195836684432515988122669320532736658636800)

theorem momentPanelPhase_owner2622P019 :
    (momentPanelPhase2622P019 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-141 / 200) 0 := by
  norm_num [momentPanelPhase2622P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P019 :
    (momentPanelGrowth2622P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P019Input : RatPair2542 := (momentPanelPhase2622P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P019Expected : RatState2542 :=
  ((((605704663814568806070796237680586083550549561439008438708307478200593 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2423994573678245943889507 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P019_replay :
    compactExp2620 momentScalarAmp2622P019Input 20 = momentScalarAmp2622P019Expected := by
  decide +kernel

theorem momentScalarAmp2622P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P019]
  have h := compactExp_real_error2620 momentPanelPhase2622P019 20 hsmall
  change |Real.exp (momentPanelPhase2622P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P019_replay] at h
  simpa only [momentPanelPhase_owner2622P019] using h

theorem momentScalarAmp2622P019_radius_le :
    (momentScalarAmp2622P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P019Expected]

def momentScalarGrow2622P019Input : RatPair2542 := (momentPanelGrowth2622P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P019Expected : RatState2542 :=
  ((((12371729363468933164976358714846060022784875513833854450281455239621099717302519259048590757028369 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15683003882609415472089096887057828703511201691683 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P019_replay :
    compactExp2620 momentScalarGrow2622P019Input 20 = momentScalarGrow2622P019Expected := by
  decide +kernel

theorem momentScalarGrow2622P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P019_replay] at h
  simpa only [momentPanelGrowth_owner2622P019] using h

theorem momentScalarGrow2622P019_radius_le :
    (momentScalarGrow2622P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P019Expected]

end ConnesWeilRH.Dev
