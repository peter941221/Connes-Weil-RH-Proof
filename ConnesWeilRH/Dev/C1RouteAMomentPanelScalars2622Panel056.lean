import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P056 : ℚ := ((-1870690507179466800378025500581434799516357886978224209 : ℚ) / 54061859003393430758678179265195756573960229722521600)

def momentPanelGrowth2622P056 : ℚ := ((1060550157254946671130632573530394093071637219150469797 : ℚ) / 3721136169597136908645831032351581553922624484854988800)

theorem momentPanelPhase_owner2622P056 :
    (momentPanelPhase2622P056 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-67 / 200) 0 := by
  norm_num [momentPanelPhase2622P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P056 :
    (momentPanelGrowth2622P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P056Input : RatPair2542 := (momentPanelPhase2622P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P056Expected : RatState2542 :=
  ((((250445404419928744955495074615471389174493208209248633744622917917031848311534725 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2539901955140909733458226065590663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P056_replay :
    compactExp2620 momentScalarAmp2622P056Input 20 = momentScalarAmp2622P056Expected := by
  decide +kernel

theorem momentScalarAmp2622P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P056]
  have h := compactExp_real_error2620 momentPanelPhase2622P056 20 hsmall
  change |Real.exp (momentPanelPhase2622P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P056_replay] at h
  simpa only [momentPanelPhase_owner2622P056] using h

theorem momentScalarAmp2622P056_radius_le :
    (momentScalarAmp2622P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P056Expected]

def momentScalarGrow2622P056Input : RatPair2542 := (momentPanelGrowth2622P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P056Expected : RatState2542 :=
  ((((2840374565208435438703063316898517860649013112159569036262687315511177267100466961403950566415769 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((450075192975209435584917436016266578774962996651 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P056_replay :
    compactExp2620 momentScalarGrow2622P056Input 20 = momentScalarGrow2622P056Expected := by
  decide +kernel

theorem momentScalarGrow2622P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P056_replay] at h
  simpa only [momentPanelGrowth_owner2622P056] using h

theorem momentScalarGrow2622P056_radius_le :
    (momentScalarGrow2622P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P056Expected]

end ConnesWeilRH.Dev
