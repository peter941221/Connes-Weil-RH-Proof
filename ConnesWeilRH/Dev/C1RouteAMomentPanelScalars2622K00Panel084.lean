import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P084 : ℚ := ((-1834955101481632153320954744686120931071025428212979033 : ℚ) / 60711691453249039036504945254054844313394722793062400)

def momentPanelGrowth2622K00P084 : ℚ := ((856607391734184746112577713619677670864970318965269151 : ℚ) / 14169900064485744391547248258556228368577583687034470400)

theorem momentPanelPhase_owner2622K00P084 :
    (momentPanelPhase2622K00P084 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P084 :
    (momentPanelGrowth2622K00P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P084Input : RatPair2542 := (momentPanelPhase2622K00P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P084Expected : RatState2542 :=
  ((((39938051209928243905989354610291796376808023630345752021281638102205752131967641333 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((101257907786426751076076761666057933 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P084_replay :
    compactExp2620 momentScalarAmp2622K00P084Input 20 = momentScalarAmp2622K00P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K00P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P084_replay] at h
  simpa only [momentPanelPhase_owner2622K00P084] using h

theorem momentScalarAmp2622K00P084_radius_le :
    (momentScalarAmp2622K00P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P084Expected]

def momentScalarGrow2622K00P084Input : RatPair2542 := (momentPanelGrowth2622K00P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P084Expected : RatState2542 :=
  ((((2269095872687513176936995065470362548668370004026826626295176092905955350732469275733512467957361 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2876420579156037919836517878512891866243929017901 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P084_replay :
    compactExp2620 momentScalarGrow2622K00P084Input 20 = momentScalarGrow2622K00P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P084] using h

theorem momentScalarGrow2622K00P084_radius_le :
    (momentScalarGrow2622K00P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P084Expected]

end ConnesWeilRH.Dev
