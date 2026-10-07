import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P134 : ℚ := ((-1774301877401384526331396043990038501339940756387468133 : ℚ) / 48836990649935452826100005988235044778690270881382400)

def momentPanelGrowth2622P134 : ℚ := ((104273122734637002421033527138792718119393086954765431 : ℚ) / 232381043931921893530195581659440119317511486727782400)

theorem momentPanelPhase_owner2622P134 :
    (momentPanelPhase2622P134 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (89 / 200) 0 := by
  norm_num [momentPanelPhase2622P134, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P134 :
    (momentPanelGrowth2622P134 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P134, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P134Input : RatPair2542 := (momentPanelPhase2622P134 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P134Expected : RatState2542 :=
  ((((88948744570154615132018871875533432302352010420342766904464962013152563777304031 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((451039347553159022006931597920649 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P134_replay :
    compactExp2620 momentScalarAmp2622P134Input 20 = momentScalarAmp2622P134Expected := by
  decide +kernel

theorem momentScalarAmp2622P134_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (89 / 200) 0) -
      (momentScalarAmp2622P134Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P134]
  have h := compactExp_real_error2620 momentPanelPhase2622P134 20 hsmall
  change |Real.exp (momentPanelPhase2622P134 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P134Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P134_replay] at h
  simpa only [momentPanelPhase_owner2622P134] using h

theorem momentScalarAmp2622P134_radius_le :
    (momentScalarAmp2622P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P134Expected]

def momentScalarGrow2622P134Input : RatPair2542 := (momentPanelGrowth2622P134 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P134Expected : RatState2542 :=
  ((((1672798213670289099819654781769243788864582356063166469240859688855990417631963502684644576165575 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4241045504372747817207159920877145105771438714693 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P134_replay :
    compactExp2620 momentScalarGrow2622P134Input 20 = momentScalarGrow2622P134Expected := by
  decide +kernel

theorem momentScalarGrow2622P134_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P134Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P134]
  have h := compactExp_real_error2620 momentPanelGrowth2622P134 20 hsmall
  change |Real.exp (momentPanelGrowth2622P134 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P134Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P134_replay] at h
  simpa only [momentPanelGrowth_owner2622P134] using h

theorem momentScalarGrow2622P134_radius_le :
    (momentScalarGrow2622P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P134Expected]

end ConnesWeilRH.Dev
