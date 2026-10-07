import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P044 : ℚ := ((-1880030407603825106971852581530958872656039186693597353 : ℚ) / 48288927535936364231773624175966438646319296177766400)

def momentPanelGrowth2622P044 : ℚ := ((1384606915966087903240758596757630483239663921611132037 : ℚ) / 2957136188682407408154854786049144605397485748014284800)

theorem momentPanelPhase_owner2622P044 :
    (momentPanelPhase2622P044 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-91 / 200) 0 := by
  norm_num [momentPanelPhase2622P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P044 :
    (momentPanelGrowth2622P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P044Input : RatPair2542 := (momentPanelPhase2622P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P044Expected : RatState2542 :=
  ((((26377474183848191654448451100908874342592194719799824869171281908626312348739801 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16719332466210268030412159061119 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P044_replay :
    compactExp2620 momentScalarAmp2622P044Input 20 = momentScalarAmp2622P044Expected := by
  decide +kernel

theorem momentScalarAmp2622P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P044]
  have h := compactExp_real_error2620 momentPanelPhase2622P044 20 hsmall
  change |Real.exp (momentPanelPhase2622P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P044_replay] at h
  simpa only [momentPanelPhase_owner2622P044] using h

theorem momentScalarAmp2622P044_radius_le :
    (momentScalarAmp2622P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622P044Expected]

def momentScalarGrow2622P044Input : RatPair2542 := (momentPanelGrowth2622P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P044Expected : RatState2542 :=
  ((((3411508157931788610684134815008501309435936095827434235112344145497483953701333196622045804589979 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4324598433001843288925407169469694658762235200929 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P044_replay :
    compactExp2620 momentScalarGrow2622P044Input 20 = momentScalarGrow2622P044Expected := by
  decide +kernel

theorem momentScalarGrow2622P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P044_replay] at h
  simpa only [momentPanelGrowth_owner2622P044] using h

theorem momentScalarGrow2622P044_radius_le :
    (momentScalarGrow2622P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P044Expected]

end ConnesWeilRH.Dev
