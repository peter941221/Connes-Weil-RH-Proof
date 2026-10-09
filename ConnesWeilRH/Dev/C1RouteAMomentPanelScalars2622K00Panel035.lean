import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P035 : ℚ := ((-1883318244363012516820342058271305579754149919145572447 : ℚ) / 42808296395945478288509806053280377322609549141606400)

def momentPanelGrowth2622K00P035 : ℚ := ((41624730863388413161156100735530965301429349941273037 : ℚ) / 59252473412226465654110953678889680485957002644684800)

theorem momentPanelPhase_owner2622K00P035 :
    (momentPanelPhase2622K00P035 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-109 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P035 :
    (momentPanelGrowth2622K00P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P035Input : RatPair2542 := (momentPanelPhase2622K00P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P035Expected : RatState2542 :=
  ((((167164937300430128265291438855889709559763145124181363858819362683190818038389 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((211918041939465433483592418605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P035_replay :
    compactExp2620 momentScalarAmp2622K00P035Input 20 = momentScalarAmp2622K00P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K00P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P035_replay] at h
  simpa only [momentPanelPhase_owner2622K00P035] using h

theorem momentScalarAmp2622K00P035_radius_le :
    (momentScalarAmp2622K00P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [momentScalarAmp2622K00P035Expected]

def momentScalarGrow2622K00P035Input : RatPair2542 := (momentPanelGrowth2622K00P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P035Expected : RatState2542 :=
  ((((1078026729674004543276798822487000757477471289198683040305769293169149057171849772843122674516463 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5466241261601405623544427341073733232345669027105 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P035_replay :
    compactExp2620 momentScalarGrow2622K00P035Input 20 = momentScalarGrow2622K00P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P035] using h

theorem momentScalarGrow2622K00P035_radius_le :
    (momentScalarGrow2622K00P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P035Expected]

end ConnesWeilRH.Dev
