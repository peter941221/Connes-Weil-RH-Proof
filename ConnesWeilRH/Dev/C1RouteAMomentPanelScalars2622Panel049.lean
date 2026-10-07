import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P049 : ℚ := ((-5630264837013903916040220458781042952082091482498495289 : ℚ) / 152722353908462695880665678503749337169608525951795200)

def momentPanelGrowth2622P049 : ℚ := ((19999908324281506295238590212842134445487836049691956477 : ℚ) / 52679340111578721495524355131400033055555609271520460800)

theorem momentPanelPhase_owner2622P049 :
    (momentPanelPhase2622P049 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-81 / 200) 0 := by
  norm_num [momentPanelPhase2622P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P049 :
    (momentPanelGrowth2622P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P049Input : RatPair2542 := (momentPanelPhase2622P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P049Expected : RatState2542 :=
  ((((208396790357198518737867040669066342315579646948840880857439733976935621283160637 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((264183606849434665428799638964275 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P049_replay :
    compactExp2620 momentScalarAmp2622P049Input 20 = momentScalarAmp2622P049Expected := by
  decide +kernel

theorem momentScalarAmp2622P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P049]
  have h := compactExp_real_error2620 momentPanelPhase2622P049 20 hsmall
  change |Real.exp (momentPanelPhase2622P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P049_replay] at h
  simpa only [momentPanelPhase_owner2622P049] using h

theorem momentScalarAmp2622P049_radius_le :
    (momentScalarAmp2622P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P049Expected]

def momentScalarGrow2622P049Input : RatPair2542 := (momentPanelGrowth2622P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P049Expected : RatState2542 :=
  ((((3122339587285021855128935365841298603679928658994188629521514952087598548884549950887388332435501 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3958034218868272358519267249985200589876815925169 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P049_replay :
    compactExp2620 momentScalarGrow2622P049Input 20 = momentScalarGrow2622P049Expected := by
  decide +kernel

theorem momentScalarGrow2622P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P049_replay] at h
  simpa only [momentPanelGrowth_owner2622P049] using h

theorem momentScalarGrow2622P049_radius_le :
    (momentScalarGrow2622P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P049Expected]

end ConnesWeilRH.Dev
