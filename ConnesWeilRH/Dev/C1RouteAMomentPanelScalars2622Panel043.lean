import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P043 : ℚ := ((-5641705143285362154119741156453825112459568427739695853 : ℚ) / 143186055724878554339386634970275590466353566108876800)

def momentPanelGrowth2622P043 : ℚ := ((22583585106201376890824306399054785038153959922897941917 : ℚ) / 46204522482793488842152480401258720207724914123001036800)

theorem momentPanelPhase_owner2622P043 :
    (momentPanelPhase2622P043 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-93 / 200) 0 := by
  norm_num [momentPanelPhase2622P043, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P043 :
    (momentPanelGrowth2622P043 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P043, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P043Input : RatPair2542 := (momentPanelPhase2622P043 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P043Expected : RatState2542 :=
  ((((516079526345045838237108081903184146305189175159942986247623114176794863272017 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((20935461755217037994345511638255 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P043_replay :
    compactExp2620 momentScalarAmp2622P043Input 20 = momentScalarAmp2622P043Expected := by
  decide +kernel

theorem momentScalarAmp2622P043_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-93 / 200) 0) -
      (momentScalarAmp2622P043Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P043]
  have h := compactExp_real_error2620 momentPanelPhase2622P043 20 hsmall
  change |Real.exp (momentPanelPhase2622P043 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P043Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P043_replay] at h
  simpa only [momentPanelPhase_owner2622P043] using h

theorem momentScalarAmp2622P043_radius_le :
    (momentScalarAmp2622P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622P043Expected]

def momentScalarGrow2622P043Input : RatPair2542 := (momentPanelGrowth2622P043 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P043Expected : RatState2542 :=
  ((((3482335517679248403050978837981989888900807276492088096227970023342248814419570356293294529467309 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4414382651498730795028260587247708024248597054799 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P043_replay :
    compactExp2620 momentScalarGrow2622P043Input 20 = momentScalarGrow2622P043Expected := by
  decide +kernel

theorem momentScalarGrow2622P043_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P043Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P043]
  have h := compactExp_real_error2620 momentPanelGrowth2622P043 20 hsmall
  change |Real.exp (momentPanelGrowth2622P043 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P043Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P043_replay] at h
  simpa only [momentPanelGrowth_owner2622P043] using h

theorem momentScalarGrow2622P043_radius_le :
    (momentScalarGrow2622P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P043Expected]

end ConnesWeilRH.Dev
