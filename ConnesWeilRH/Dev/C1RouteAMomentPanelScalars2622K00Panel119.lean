import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P119 : ℚ := ((-1787199871960101543794964920801691989698913648573552503 : ℚ) / 55596435722590878822792048339547853744598958892646400)

def momentPanelGrowth2622K00P119 : ℚ := ((4567955228213430965418111884631595451387932070896351 : ℚ) / 18910461029276886040069865780818030759016839669350400)

theorem momentPanelPhase_owner2622K00P119 :
    (momentPanelPhase2622K00P119 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (59 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P119 :
    (momentPanelGrowth2622K00P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P119Input : RatPair2542 := (momentPanelPhase2622K00P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P119Expected : RatState2542 :=
  ((((23377217078905655941538353686440491497554852628463561809426714135791075143111405099 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29635051764917432668794440175468493 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P119_replay :
    compactExp2620 momentScalarAmp2622K00P119Input 20 = momentScalarAmp2622K00P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K00P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P119_replay] at h
  simpa only [momentPanelPhase_owner2622K00P119] using h

theorem momentScalarAmp2622K00P119_radius_le :
    (momentScalarAmp2622K00P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P119Expected]

def momentScalarGrow2622K00P119Input : RatPair2542 := (momentPanelGrowth2622K00P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P119Expected : RatState2542 :=
  ((((679900743548451992479357720770454257755672488234485171711369522079300298634313095880621878151207 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3447505548428494395636063829679634043378230744743 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P119_replay :
    compactExp2620 momentScalarGrow2622K00P119Input 20 = momentScalarGrow2622K00P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P119] using h

theorem momentScalarGrow2622K00P119_radius_le :
    (momentScalarGrow2622K00P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P119Expected]

end ConnesWeilRH.Dev
