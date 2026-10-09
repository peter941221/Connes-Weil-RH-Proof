import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P165 : ℚ := ((-1779052595455448479729100853997925296551066446585995307 : ℚ) / 26183715271306457593942891081132657974023316465254400)

def momentPanelGrowth2622K00P165 : ℚ := ((2138624642426881453293520349803295702019213147718973 : ℚ) / 828945459923621498918652491056266775211099239219200)

theorem momentPanelPhase_owner2622K00P165 :
    (momentPanelPhase2622K00P165 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (151 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P165, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P165 :
    (momentPanelGrowth2622K00P165 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P165, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P165Input : RatPair2542 := (momentPanelPhase2622K00P165 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P165Expected : RatState2542 :=
  ((((3314583975211653538543402641091283848007054984285276276985876105501 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417860043242538834054387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P165_replay :
    compactExp2620 momentScalarAmp2622K00P165Input 20 = momentScalarAmp2622K00P165Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P165_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (151 / 200) 0) -
      (momentScalarAmp2622K00P165Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P165]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P165 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P165 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P165Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P165_replay] at h
  simpa only [momentPanelPhase_owner2622K00P165] using h

theorem momentScalarAmp2622K00P165_radius_le :
    (momentScalarAmp2622K00P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P165Expected]

def momentScalarGrow2622K00P165Input : RatPair2542 := (momentPanelGrowth2622K00P165 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P165Expected : RatState2542 :=
  ((((28187057865082686199617884640134560725837049291386810616774622311021839413897873119893039251721235 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((35731252907454309697466887310807577921831416924371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P165_replay :
    compactExp2620 momentScalarGrow2622K00P165Input 20 = momentScalarGrow2622K00P165Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P165_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P165Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P165]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P165 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P165 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P165Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P165_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P165] using h

theorem momentScalarGrow2622K00P165_radius_le :
    (momentScalarGrow2622K00P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622K00P165Expected]

end ConnesWeilRH.Dev
