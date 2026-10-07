import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P020 : ℚ := ((-1879808544640070416681306932799748865334971661379769817 : ℚ) / 31481658706630980672431248599729183920276071933542400)

def momentPanelGrowth2622P020 : ℚ := ((3244932040220940891016545992373412020678015895700357 : ℚ) / 1979877999321707547004054296820339653190146116812800)

theorem momentPanelPhase_owner2622P020 :
    (momentPanelPhase2622P020 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-139 / 200) 0 := by
  norm_num [momentPanelPhase2622P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P020 :
    (momentPanelGrowth2622P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P020Input : RatPair2542 := (momentPanelPhase2622P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P020Expected : RatState2542 :=
  ((((12482776211627084103041356785631775836150387573103490425585117950472145 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2449501038969987187043543 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P020_replay :
    compactExp2620 momentScalarAmp2622P020Input 20 = momentScalarAmp2622P020Expected := by
  decide +kernel

theorem momentScalarAmp2622P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P020]
  have h := compactExp_real_error2620 momentPanelPhase2622P020 20 hsmall
  change |Real.exp (momentPanelPhase2622P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P020_replay] at h
  simpa only [momentPanelPhase_owner2622P020] using h

theorem momentScalarAmp2622P020_radius_le :
    (momentScalarAmp2622P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P020Expected]

def momentScalarGrow2622P020Input : RatPair2542 := (momentPanelGrowth2622P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P020Expected : RatState2542 :=
  ((((10999880446440829857464950037944791437213274583792958229173327480252561830208791058218252582724889 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((13943983255490865237715389150448193401092727393881 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P020_replay :
    compactExp2620 momentScalarGrow2622P020Input 20 = momentScalarGrow2622P020Expected := by
  decide +kernel

theorem momentScalarGrow2622P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P020_replay] at h
  simpa only [momentPanelGrowth_owner2622P020] using h

theorem momentScalarGrow2622P020_radius_le :
    (momentScalarGrow2622P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P020Expected]

end ConnesWeilRH.Dev
