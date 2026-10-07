import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P088 : ℚ := ((-5487259019809247860153168997992201315823898981995615283 : ℚ) / 182646599932812933130886125453615231997063744769228800)

def momentPanelGrowth2622P088 : ℚ := ((172091105459815803870142434134489344804082827474797157 : ℚ) / 4753687076371419820356734366665635507309540826467532800)

theorem momentPanelPhase_owner2622P088 :
    (momentPanelPhase2622P088 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-3 / 200) 0 := by
  norm_num [momentPanelPhase2622P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P088 :
    (momentPanelGrowth2622P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P088Input : RatPair2542 := (momentPanelPhase2622P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P088Expected : RatState2542 :=
  ((((95728738100702764447645266346348677444749857416347771872838368906731007865258832421 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15169258651584681205911430974412315 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622P088_replay :
    compactExp2620 momentScalarAmp2622P088Input 20 = momentScalarAmp2622P088Expected := by
  decide +kernel

theorem momentScalarAmp2622P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P088]
  have h := compactExp_real_error2620 momentPanelPhase2622P088 20 hsmall
  change |Real.exp (momentPanelPhase2622P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P088_replay] at h
  simpa only [momentPanelPhase_owner2622P088] using h

theorem momentScalarAmp2622P088_radius_le :
    (momentScalarAmp2622P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P088Expected]

def momentScalarGrow2622P088Input : RatPair2542 := (momentPanelGrowth2622P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P088Expected : RatState2542 :=
  ((((2214729906123260704337744520618114228159390442930106325847956592504735826622801817951948010262687 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2807503597912785126695148223902623760922343890109 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P088_replay :
    compactExp2620 momentScalarGrow2622P088Input 20 = momentScalarGrow2622P088Expected := by
  decide +kernel

theorem momentScalarGrow2622P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P088_replay] at h
  simpa only [momentPanelGrowth_owner2622P088] using h

theorem momentScalarGrow2622P088_radius_le :
    (momentScalarGrow2622P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P088Expected]

end ConnesWeilRH.Dev
