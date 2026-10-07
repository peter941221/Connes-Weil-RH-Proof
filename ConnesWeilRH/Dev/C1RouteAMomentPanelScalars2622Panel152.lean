import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P152 : ℚ := ((-113329221463550204351347782750606805947626708667465 : ℚ) / 2374940160662717242080987853163959906940890382336)

def momentPanelGrowth2622P152 : ℚ := ((88329356024576016232175939720154340126043948241422820631 : ℚ) / 83061159462614181154076278869813884904542918444213862400)

theorem momentPanelPhase_owner2622P152 :
    (momentPanelPhase2622P152 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (5 / 8) 0 := by
  norm_num [momentPanelPhase2622P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P152 :
    (momentPanelGrowth2622P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P152Input : RatPair2542 := (momentPanelPhase2622P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P152Expected : RatState2542 :=
  ((((4032742130031861295944297485311039316717351176188744267897585853618305025517 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5114758481285263746459678707 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P152_replay :
    compactExp2620 momentScalarAmp2622P152Input 20 = momentScalarAmp2622P152Expected := by
  decide +kernel

theorem momentScalarAmp2622P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P152]
  have h := compactExp_real_error2620 momentPanelPhase2622P152 20 hsmall
  change |Real.exp (momentPanelPhase2622P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P152_replay] at h
  simpa only [momentPanelPhase_owner2622P152] using h

theorem momentScalarAmp2622P152_radius_le :
    (momentScalarAmp2622P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [momentScalarAmp2622P152Expected]

def momentScalarGrow2622P152Input : RatPair2542 := (momentPanelGrowth2622P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P152Expected : RatState2542 :=
  ((((6186406368221818103938109907461573910936309633992441895522558651441690510859744135910864565824925 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7842193792676305845534990830703486390920387449673 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P152_replay :
    compactExp2620 momentScalarGrow2622P152Input 20 = momentScalarGrow2622P152Expected := by
  decide +kernel

theorem momentScalarGrow2622P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P152_replay] at h
  simpa only [momentPanelGrowth_owner2622P152] using h

theorem momentScalarGrow2622P152_radius_le :
    (momentScalarGrow2622P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P152Expected]

end ConnesWeilRH.Dev
