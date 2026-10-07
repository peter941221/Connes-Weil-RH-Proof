import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P143 : ℚ := ((-1770620255979437297660444071194894749375154396336647751 : ℚ) / 43465972132744384601701464228002704681454718785945600)

def momentPanelGrowth2622P143 : ℚ := ((4797554460597819120597294014165031217003692229794499711 : ℚ) / 7162365088893397624490130406889830360082301126600294400)

theorem momentPanelPhase_owner2622P143 :
    (momentPanelPhase2622P143 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (107 / 200) 0 := by
  norm_num [momentPanelPhase2622P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P143 :
    (momentPanelGrowth2622P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P143Input : RatPair2542 := (momentPanelPhase2622P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P143Expected : RatState2542 :=
  ((((2173924062582106797887126287491555491896265472548229293605624087115071138551523 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5511768824033862308286663979453 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P143_replay :
    compactExp2620 momentScalarAmp2622P143Input 20 = momentScalarAmp2622P143Expected := by
  decide +kernel

theorem momentScalarAmp2622P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P143]
  have h := compactExp_real_error2620 momentPanelPhase2622P143 20 hsmall
  change |Real.exp (momentPanelPhase2622P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P143_replay] at h
  simpa only [momentPanelPhase_owner2622P143] using h

theorem momentScalarAmp2622P143_radius_le :
    (momentScalarAmp2622P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622P143Expected]

def momentScalarGrow2622P143Input : RatPair2542 := (momentPanelGrowth2622P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P143Expected : RatState2542 :=
  ((((4173508712876383870611694848327423274229100387621120395569986370032605758020983899614098748902387 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5290547445343304106789188937369451588119360813167 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P143_replay :
    compactExp2620 momentScalarGrow2622P143Input 20 = momentScalarGrow2622P143Expected := by
  decide +kernel

theorem momentScalarGrow2622P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P143_replay] at h
  simpa only [momentPanelGrowth_owner2622P143] using h

theorem momentScalarGrow2622P143_radius_le :
    (momentScalarGrow2622P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P143Expected]

end ConnesWeilRH.Dev
