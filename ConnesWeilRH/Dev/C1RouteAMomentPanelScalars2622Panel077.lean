import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P077 : ℚ := ((-118080270986185504397893049405004373082040846363971 : ℚ) / 3836441797993620160284672685880242926596822925312)

def momentPanelGrowth2622P077 : ℚ := ((7717125981511206583116551196897532269065481717170076077 : ℚ) / 73568765701653983268274397906017955790875310099844300800)

theorem momentPanelPhase_owner2622P077 :
    (momentPanelPhase2622P077 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 8) 0 := by
  norm_num [momentPanelPhase2622P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P077 :
    (momentPanelGrowth2622P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P077Input : RatPair2542 := (momentPanelPhase2622P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P077Expected : RatState2542 :=
  ((((91754338367328092249581745589279115375133346850825043690659415810558256803390564395 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((116315856247590658607725306088176393 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P077_replay :
    compactExp2620 momentScalarAmp2622P077Input 20 = momentScalarAmp2622P077Expected := by
  decide +kernel

theorem momentScalarAmp2622P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P077]
  have h := compactExp_real_error2620 momentPanelPhase2622P077 20 hsmall
  change |Real.exp (momentPanelPhase2622P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P077_replay] at h
  simpa only [momentPanelPhase_owner2622P077] using h

theorem momentScalarAmp2622P077_radius_le :
    (momentScalarAmp2622P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P077Expected]

def momentScalarGrow2622P077Input : RatPair2542 := (momentPanelGrowth2622P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P077Expected : RatState2542 :=
  ((((1186109285203291691392991715810785416625629763259450889358245344468738294064008882629238534043193 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1503571996910853406152020795339352892350059552213 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P077_replay :
    compactExp2620 momentScalarGrow2622P077Input 20 = momentScalarGrow2622P077Expected := by
  decide +kernel

theorem momentScalarGrow2622P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P077_replay] at h
  simpa only [momentPanelGrowth_owner2622P077] using h

theorem momentScalarGrow2622P077_radius_le :
    (momentScalarGrow2622P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P077Expected]

end ConnesWeilRH.Dev
