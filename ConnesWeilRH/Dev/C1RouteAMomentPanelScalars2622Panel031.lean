import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P031 : ℚ := ((-5650695896814568657268287236412002759735418362917372277 : ℚ) / 120167404936916833377678598854994132906772628557004800)

def momentPanelGrowth2622P031 : ℚ := ((27729021968103677660664745304187846655654059102949937677 : ℚ) / 32348938897782530088987221805296088575254302640884940800)

theorem momentPanelPhase_owner2622P031 :
    (momentPanelPhase2622P031 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-117 / 200) 0 := by
  norm_num [momentPanelPhase2622P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P031 :
    (momentPanelGrowth2622P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P031Input : RatPair2542 := (momentPanelPhase2622P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P031Expected : RatState2542 :=
  ((((1010294176413532378966296371404882088904367443932037210963717548349437114159 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((10248477480369917726390069165 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P031_replay :
    compactExp2620 momentScalarAmp2622P031Input 20 = momentScalarAmp2622P031Expected := by
  decide +kernel

theorem momentScalarAmp2622P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P031]
  have h := compactExp_real_error2620 momentPanelPhase2622P031 20 hsmall
  change |Real.exp (momentPanelPhase2622P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P031_replay] at h
  simpa only [momentPanelPhase_owner2622P031] using h

theorem momentScalarAmp2622P031_radius_le :
    (momentScalarAmp2622P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [momentScalarAmp2622P031Expected]

def momentScalarGrow2622P031Input : RatPair2542 := (momentPanelGrowth2622P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P031Expected : RatState2542 :=
  ((((1258372716047067406772604741091849273208063028287565161729431794896670569490363212446842368859689 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6380702499163232760784694195967295540530288240017 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P031_replay :
    compactExp2620 momentScalarGrow2622P031Input 20 = momentScalarGrow2622P031Expected := by
  decide +kernel

theorem momentScalarGrow2622P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P031_replay] at h
  simpa only [momentPanelGrowth_owner2622P031] using h

theorem momentScalarGrow2622P031_radius_le :
    (momentScalarGrow2622P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P031Expected]

end ConnesWeilRH.Dev
