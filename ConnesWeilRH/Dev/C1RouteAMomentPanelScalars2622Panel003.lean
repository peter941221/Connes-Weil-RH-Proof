import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P003 : ℚ := ((-1858961049824270502293346454935755931390258574333494431 : ℚ) / 15332065614124503426280531198214256553078017333657600)

def momentPanelGrowth2622P003 : ℚ := ((119530210634080126398992362791779499148196793720287453431 : ℚ) / 13495508402709865876228635438559708522695099314234982400)

theorem momentPanelPhase_owner2622P003 :
    (momentPanelPhase2622P003 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-173 / 200) 0 := by
  norm_num [momentPanelPhase2622P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P003 :
    (momentPanelGrowth2622P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P003Input : RatPair2542 := (momentPanelPhase2622P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P003Expected : RatState2542 :=
  ((((47082873736504410784611528979503538927450347 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P003_replay :
    compactExp2620 momentScalarAmp2622P003Input 20 = momentScalarAmp2622P003Expected := by
  decide +kernel

theorem momentScalarAmp2622P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P003]
  have h := compactExp_real_error2620 momentPanelPhase2622P003 20 hsmall
  change |Real.exp (momentPanelPhase2622P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P003_replay] at h
  simpa only [momentPanelPhase_owner2622P003] using h

theorem momentScalarAmp2622P003_radius_le :
    (momentScalarAmp2622P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P003Expected]

def momentScalarGrow2622P003Input : RatPair2542 := (momentPanelGrowth2622P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P003Expected : RatState2542 :=
  ((((1875299800744139798834722857185454369479321295889481082311237075459755616413726980614974749807390083 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((19017638706665182409613377534746025529550008913452513 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P003_replay :
    compactExp2620 momentScalarGrow2622P003Input 20 = momentScalarGrow2622P003Expected := by
  decide +kernel

theorem momentScalarGrow2622P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P003_replay] at h
  simpa only [momentPanelGrowth_owner2622P003] using h

theorem momentScalarGrow2622P003_radius_le :
    (momentScalarGrow2622P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [momentScalarGrow2622P003Expected]

end ConnesWeilRH.Dev
