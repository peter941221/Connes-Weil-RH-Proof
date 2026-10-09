import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P060 : ℚ := ((-1866554221367155751714247160989015559440917708866447497 : ℚ) / 55596435722590878822792048339547853744598958892646400)

def momentPanelGrowth2622K00P060 : ℚ := ((4567955228213430965418111884631595451387932070896351 : ℚ) / 18910461029276886040069865780818030759016839669350400)

theorem momentPanelPhase_owner2622K00P060 :
    (momentPanelPhase2622K00P060 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-59 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P060, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P060 :
    (momentPanelGrowth2622K00P060 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P060, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P060Input : RatPair2542 := (momentPanelPhase2622K00P060 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P060Expected : RatState2542 :=
  ((((5609344787111192351920563640675276880498175084759156826085986495128195347910026819 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7110916962143195340367954602439039 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P060_replay :
    compactExp2620 momentScalarAmp2622K00P060Input 20 = momentScalarAmp2622K00P060Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P060_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-59 / 200) 0) -
      (momentScalarAmp2622K00P060Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P060]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P060 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P060 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P060Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P060_replay] at h
  simpa only [momentPanelPhase_owner2622K00P060] using h

theorem momentScalarAmp2622K00P060_radius_le :
    (momentScalarAmp2622K00P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P060Expected]

def momentScalarGrow2622K00P060Input : RatPair2542 := (momentPanelGrowth2622K00P060 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P060Expected : RatState2542 :=
  ((((679900743548451992479357720770454257755672488234485171711369522079300298634313095880621878151207 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3447505548428494395636063829679634043378230744743 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P060_replay :
    compactExp2620 momentScalarGrow2622K00P060Input 20 = momentScalarGrow2622K00P060Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P060_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P060Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P060]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P060 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P060 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P060Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P060_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P060] using h

theorem momentScalarGrow2622K00P060_radius_le :
    (momentScalarGrow2622K00P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P060Expected]

end ConnesWeilRH.Dev
