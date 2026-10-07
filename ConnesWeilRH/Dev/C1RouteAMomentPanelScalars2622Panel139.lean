import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P139 : ℚ := ((-5315465820120278045770138701035839685810618177027654829 : ℚ) / 137924649830487303833853369572496971595592208954163200)

def momentPanelGrowth2622P139 : ℚ := ((3819488379000581715737535337176669193363580346853 : ℚ) / 6850788924988607429079772653357576654637183795200)

theorem momentPanelPhase_owner2622P139 :
    (momentPanelPhase2622P139 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (99 / 200) 0 := by
  norm_num [momentPanelPhase2622P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P139 :
    (momentPanelGrowth2622P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P139Input : RatPair2542 := (momentPanelPhase2622P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P139Expected : RatState2542 :=
  ((((19558348568005698136640871062272140284119289540840923323123694887581969986356659 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((49588129528456929734808190715683 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P139_replay :
    compactExp2620 momentScalarAmp2622P139Input 20 = momentScalarAmp2622P139Expected := by
  decide +kernel

theorem momentScalarAmp2622P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P139]
  have h := compactExp_real_error2620 momentPanelPhase2622P139 20 hsmall
  change |Real.exp (momentPanelPhase2622P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P139_replay] at h
  simpa only [momentPanelPhase_owner2622P139] using h

theorem momentScalarAmp2622P139_radius_le :
    (momentScalarAmp2622P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622P139Expected]

def momentScalarGrow2622P139Input : RatPair2542 := (momentPanelGrowth2622P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P139Expected : RatState2542 :=
  ((((1865085701389198172078186159970186155422221348674153703744198419685916180557793863878937086426175 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((591068937940762280972578515033103986767821493317 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P139_replay :
    compactExp2620 momentScalarGrow2622P139Input 20 = momentScalarGrow2622P139Expected := by
  decide +kernel

theorem momentScalarGrow2622P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P139_replay] at h
  simpa only [momentPanelGrowth_owner2622P139] using h

theorem momentScalarGrow2622P139_radius_le :
    (momentScalarGrow2622P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P139Expected]

end ConnesWeilRH.Dev
