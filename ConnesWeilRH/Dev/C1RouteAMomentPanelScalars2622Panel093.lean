import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P093 : ℚ := ((-1821727185204901438044851352380745788398951126371969851 : ℚ) / 60821304076048856755370221616508565539868917733785600)

def momentPanelGrowth2622P093 : ℚ := ((55885025776955105945506278001037969756289099210797 : ℚ) / 1157783328323074655514481578417430454633684061388800)

theorem momentPanelPhase_owner2622P093 :
    (momentPanelPhase2622P093 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 200) 0 := by
  norm_num [momentPanelPhase2622P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P093 :
    (momentPanelGrowth2622P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P093Input : RatPair2542 := (momentPanelPhase2622P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P093Expected : RatState2542 :=
  ((((209679918997285122455959829684740321661464395764080876915892200337570611021660129593 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((265808467771409136850137674880181305 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P093_replay :
    compactExp2620 momentScalarAmp2622P093Input 20 = momentScalarAmp2622P093Expected := by
  decide +kernel

theorem momentScalarAmp2622P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P093]
  have h := compactExp_real_error2620 momentPanelPhase2622P093 20 hsmall
  change |Real.exp (momentPanelPhase2622P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P093_replay] at h
  simpa only [momentPanelPhase_owner2622P093] using h

theorem momentScalarAmp2622P093_radius_le :
    (momentScalarAmp2622P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [momentScalarAmp2622P093Expected]

def momentScalarGrow2622P093Input : RatPair2542 := (momentPanelGrowth2622P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P093Expected : RatState2542 :=
  ((((140101112379854470593272806080620661539916550207065795597224972112533760671532229653100105775663 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2841588016408927863522440529021809203564614528441 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P093_replay :
    compactExp2620 momentScalarGrow2622P093Input 20 = momentScalarGrow2622P093Expected := by
  decide +kernel

theorem momentScalarGrow2622P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P093_replay] at h
  simpa only [momentPanelGrowth_owner2622P093] using h

theorem momentScalarGrow2622P093_radius_le :
    (momentScalarGrow2622P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P093Expected]

end ConnesWeilRH.Dev
