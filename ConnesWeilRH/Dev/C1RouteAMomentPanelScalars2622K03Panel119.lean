import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P119 : ℚ := ((-72880873642639151884616785112645200363124106653746025 : ℚ) / 2223857428903635152911681933581914149783958355705856)

def momentPanelGrowth2622K03P119 : ℚ := ((166658174839494133509328672849974619343777394132225 : ℚ) / 756418441171075441602794631232721230360673586774016)

theorem momentPanelPhase_owner2622K03P119 :
    (momentPanelPhase2622K03P119 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P119 :
    (momentPanelGrowth2622K03P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P119Input : RatPair2542 := (momentPanelPhase2622K03P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P119Expected : RatState2542 :=
  ((((12496234500574725607577183709578485085665719616986731676692619721115715773555704079 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7920677133438028834395799994749701 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P119_replay :
    compactExp2620 momentScalarAmp2622K03P119Input 20 = momentScalarAmp2622K03P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K03P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P119_replay] at h
  simpa only [momentPanelPhase_owner2622K03P119] using h

theorem momentScalarAmp2622K03P119_radius_le :
    (momentScalarAmp2622K03P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P119Expected]

def momentScalarGrow2622K03P119Input : RatPair2542 := (momentPanelGrowth2622K03P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P119Expected : RatState2542 :=
  ((((332808736993026007008799339884444082957947578016368404398582948689013617490030114134687632566189 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1687540426257881632872510116583601966755885324067 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P119_replay :
    compactExp2620 momentScalarGrow2622K03P119Input 20 = momentScalarGrow2622K03P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P119] using h

theorem momentScalarGrow2622K03P119_radius_le :
    (momentScalarGrow2622K03P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P119Expected]

end ConnesWeilRH.Dev
