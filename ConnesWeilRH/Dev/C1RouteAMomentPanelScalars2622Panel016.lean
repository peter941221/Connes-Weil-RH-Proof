import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P016 : ℚ := ((-5629984083133973304472353679186419133056776451710429667 : ℚ) / 83995239412976986152137399245266128170288298118348800)

def momentPanelGrowth2622P016 : ℚ := ((2135882233493284550488894590750004144378342223636280277 : ℚ) / 973695779119705785287679007449059012346928295627980800)

theorem momentPanelPhase_owner2622P016 :
    (momentPanelPhase2622P016 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-147 / 200) 0 := by
  norm_num [momentPanelPhase2622P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P016 :
    (momentPanelGrowth2622P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P016Input : RatPair2542 := (momentPanelPhase2622P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P016Expected : RatState2542 :=
  ((((2074295076467380059518106649619338232962398506226976347873593363163 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417872676425165254324683 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P016_replay :
    compactExp2620 momentScalarAmp2622P016Input 20 = momentScalarAmp2622P016Expected := by
  decide +kernel

theorem momentScalarAmp2622P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P016]
  have h := compactExp_real_error2620 momentPanelPhase2622P016 20 hsmall
  change |Real.exp (momentPanelPhase2622P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P016_replay] at h
  simpa only [momentPanelPhase_owner2622P016] using h

theorem momentScalarAmp2622P016_radius_le :
    (momentScalarAmp2622P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P016Expected]

def momentScalarGrow2622P016Input : RatPair2542 := (momentPanelGrowth2622P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P016Expected : RatState2542 :=
  ((((9576999985411913532585527608462108547838667487992331483405032881392232877095085021920844710911511 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3035066095719158966108835536797273300161962396893 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P016_replay :
    compactExp2620 momentScalarGrow2622P016Input 20 = momentScalarGrow2622P016Expected := by
  decide +kernel

theorem momentScalarGrow2622P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P016_replay] at h
  simpa only [momentPanelGrowth_owner2622P016] using h

theorem momentScalarGrow2622P016_radius_le :
    (momentScalarGrow2622P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P016Expected]

end ConnesWeilRH.Dev
