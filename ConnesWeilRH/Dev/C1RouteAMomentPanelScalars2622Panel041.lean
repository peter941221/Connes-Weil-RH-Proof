import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P041 : ℚ := ((-1881520137852980729077144903165871486555418391776434339 : ℚ) / 46571663112072553302884294497524806098223575439769600)

def momentPanelGrowth2622P041 : ℚ := ((23442609748860925341052246328294142998407376494053865757 : ℚ) / 43955271462941229251037009443708360640474433939360972800)

theorem momentPanelPhase_owner2622P041 :
    (momentPanelPhase2622P041 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-97 / 200) 0 := by
  norm_num [momentPanelPhase2622P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P041 :
    (momentPanelGrowth2622P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P041Input : RatPair2542 := (momentPanelPhase2622P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P041Expected : RatState2542 :=
  ((((3039757224428868712802025687565263333601680872405186177782175399548636286314429 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((7706999494852135068801922161217 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P041_replay :
    compactExp2620 momentScalarAmp2622P041Input 20 = momentScalarAmp2622P041Expected := by
  decide +kernel

theorem momentScalarAmp2622P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P041]
  have h := compactExp_real_error2620 momentPanelPhase2622P041 20 hsmall
  change |Real.exp (momentPanelPhase2622P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P041_replay] at h
  simpa only [momentPanelPhase_owner2622P041] using h

theorem momentScalarAmp2622P041_radius_le :
    (momentScalarAmp2622P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622P041Expected]

def momentScalarGrow2622P041Input : RatPair2542 := (momentPanelGrowth2622P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P041Expected : RatState2542 :=
  ((((227562324135916023688696430373851944920107904721610321913524018328447011184426947495417723141033 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((4615509920933455336394872048522411269579541873323 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P041_replay :
    compactExp2620 momentScalarGrow2622P041Input 20 = momentScalarGrow2622P041Expected := by
  decide +kernel

theorem momentScalarGrow2622P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P041_replay] at h
  simpa only [momentPanelGrowth_owner2622P041] using h

theorem momentScalarGrow2622P041_radius_le :
    (momentScalarGrow2622P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P041Expected]

end ConnesWeilRH.Dev
