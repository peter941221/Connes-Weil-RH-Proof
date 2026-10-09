import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P135 : ℚ := ((-1773723685723432188537359500259748676483792170746402647 : ℚ) / 48288927535936364231773624175966438646319296177766400)

def momentPanelGrowth2622K00P135 : ℚ := ((1384606915966087903240758596757630483239663921611132037 : ℚ) / 2957136188682407408154854786049144605397485748014284800)

theorem momentPanelPhase_owner2622K00P135 :
    (momentPanelPhase2622K00P135 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (91 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P135, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P135 :
    (momentPanelGrowth2622K00P135 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P135, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P135Input : RatPair2542 := (momentPanelPhase2622K00P135 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P135Expected : RatState2542 :=
  ((((119203869309551400661197503444138729338030637611572842810842743098823112261740503 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((302228302209218398942243327767533 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P135_replay :
    compactExp2620 momentScalarAmp2622K00P135Input 20 = momentScalarAmp2622K00P135Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P135_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (91 / 200) 0) -
      (momentScalarAmp2622K00P135Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P135]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P135 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P135 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P135Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P135_replay] at h
  simpa only [momentPanelPhase_owner2622K00P135] using h

theorem momentScalarAmp2622K00P135_radius_le :
    (momentScalarAmp2622K00P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622K00P135Expected]

def momentScalarGrow2622K00P135Input : RatPair2542 := (momentPanelGrowth2622K00P135 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P135Expected : RatState2542 :=
  ((((3411508157931788610684134815008501309435936095827434235112344145497483953701333196622045804589979 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4324598433001843288925407169469694658762235200929 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P135_replay :
    compactExp2620 momentScalarGrow2622K00P135Input 20 = momentScalarGrow2622K00P135Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P135_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P135Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P135]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P135 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P135 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P135Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P135_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P135] using h

theorem momentScalarGrow2622K00P135_radius_le :
    (momentScalarGrow2622K00P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P135Expected]

end ConnesWeilRH.Dev
