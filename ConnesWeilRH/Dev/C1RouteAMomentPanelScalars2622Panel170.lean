import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P170 : ℚ := ((-1785135596187278397032881078548108042099558780327417117 : ℚ) / 21433834949981023109780915374804738160141535700582400)

def momentPanelGrowth2622P170 : ℚ := ((111636144970413008704601362130813247032767557772846501591 : ℚ) / 27007456415243396080751252638229924110169109657183846400)

theorem momentPanelPhase_owner2622P170 :
    (momentPanelPhase2622P170 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (161 / 200) 0 := by
  norm_num [momentPanelPhase2622P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P170 :
    (momentPanelGrowth2622P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P170Input : RatPair2542 := (momentPanelPhase2622P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P170Expected : RatState2542 :=
  ((((360532781798971581219306399251130920192259731416213831158823 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((151115727451942913561473 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622P170_replay :
    compactExp2620 momentScalarAmp2622P170Input 20 = momentScalarAmp2622P170Expected := by
  decide +kernel

theorem momentScalarAmp2622P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P170]
  have h := compactExp_real_error2620 momentPanelPhase2622P170 20 hsmall
  change |Real.exp (momentPanelPhase2622P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P170_replay] at h
  simpa only [momentPanelPhase_owner2622P170] using h

theorem momentScalarAmp2622P170_radius_le :
    (momentScalarAmp2622P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P170Expected]

def momentScalarGrow2622P170Input : RatPair2542 := (momentPanelGrowth2622P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P170Expected : RatState2542 :=
  ((((133280956808721489616461612332715178362458099689047779951183059083436708945268178358741094583811453 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((84476509438189870295833123474781305676297002265541 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P170_replay :
    compactExp2620 momentScalarGrow2622P170Input 20 = momentScalarGrow2622P170Expected := by
  decide +kernel

theorem momentScalarGrow2622P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P170_replay] at h
  simpa only [momentPanelGrowth_owner2622P170] using h

theorem momentScalarGrow2622P170_radius_le :
    (momentScalarGrow2622P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622P170Expected]

end ConnesWeilRH.Dev
