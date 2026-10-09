import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P159 : ℚ := ((-1773945548687186878827905148990958683804859696060230183 : ℚ) / 31481658706630980672431248599729183920276071933542400)

def momentPanelGrowth2622K00P159 : ℚ := ((3244932040220940891016545992373412020678015895700357 : ℚ) / 1979877999321707547004054296820339653190146116812800)

theorem momentPanelPhase_owner2622K00P159 :
    (momentPanelPhase2622K00P159 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (139 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P159 :
    (momentPanelGrowth2622K00P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P159Input : RatPair2542 := (momentPanelPhase2622K00P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P159Expected : RatState2542 :=
  ((((720672620901205417090957301285149522104366040904759578527735142128333305 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1665730907046564927348113 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P159_replay :
    compactExp2620 momentScalarAmp2622K00P159Input 20 = momentScalarAmp2622K00P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K00P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P159_replay] at h
  simpa only [momentPanelPhase_owner2622K00P159] using h

theorem momentScalarAmp2622K00P159_radius_le :
    (momentScalarAmp2622K00P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622K00P159Expected]

def momentScalarGrow2622K00P159Input : RatPair2542 := (momentPanelGrowth2622K00P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P159Expected : RatState2542 :=
  ((((10999880446440829857464950037944791437213274583792958229173327480252561830208791058218252582724889 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((13943983255490865237715389150448193401092727393881 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P159_replay :
    compactExp2620 momentScalarGrow2622K00P159Input 20 = momentScalarGrow2622K00P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P159] using h

theorem momentScalarGrow2622K00P159_radius_le :
    (momentScalarGrow2622K00P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P159Expected]

end ConnesWeilRH.Dev
