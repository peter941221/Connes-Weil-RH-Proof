import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P022 : ℚ := ((-45144240185320277676280370980459043918747944617288507 : ℚ) / 795604953822010276097130930809926568825198278082560)

def momentPanelGrowth2622P022 : ℚ := ((482011815466768638348821852807689802569047540481237 : ℚ) / 335688657324441764024908860014521256077222005964800)

theorem momentPanelPhase_owner2622P022 :
    (momentPanelPhase2622P022 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 40) 0 := by
  norm_num [momentPanelPhase2622P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P022 :
    (momentPanelGrowth2622P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P022Input : RatPair2542 := (momentPanelPhase2622P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P022Expected : RatState2542 :=
  ((((243118541036807280091657386691379963433682601844498946133916995225137091 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3034263723436888531727103 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P022_replay :
    compactExp2620 momentScalarAmp2622P022Input 20 = momentScalarAmp2622P022Expected := by
  decide +kernel

theorem momentScalarAmp2622P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P022]
  have h := compactExp_real_error2620 momentPanelPhase2622P022 20 hsmall
  change |Real.exp (momentPanelPhase2622P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P022_replay] at h
  simpa only [momentPanelPhase_owner2622P022] using h

theorem momentScalarAmp2622P022_radius_le :
    (momentScalarAmp2622P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622P022Expected]

def momentScalarGrow2622P022Input : RatPair2542 := (momentPanelGrowth2622P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P022Expected : RatState2542 :=
  ((((8978369927176125375716195033820573571343394134580793668897644740839022834234566829507313278916929 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11381420441858942237884963615105029984251672091071 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P022_replay :
    compactExp2620 momentScalarGrow2622P022Input 20 = momentScalarGrow2622P022Expected := by
  decide +kernel

theorem momentScalarGrow2622P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P022_replay] at h
  simpa only [momentPanelGrowth_owner2622P022] using h

theorem momentScalarGrow2622P022_radius_le :
    (momentScalarGrow2622P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P022Expected]

end ConnesWeilRH.Dev
