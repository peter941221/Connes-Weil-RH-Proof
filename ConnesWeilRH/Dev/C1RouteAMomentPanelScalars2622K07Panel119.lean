import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P119 : ℚ := ((-30099697819457299253921337200071992475 : ℚ) / 987591088421007136282839559618691072)

def momentPanelGrowth2622K07P119 : ℚ := ((100137291110742106751991679141464675 : ℚ) / 335917267855678965561414375798996992)

theorem momentPanelPhase_owner2622K07P119 :
    (momentPanelPhase2622K07P119 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P119 :
    (momentPanelGrowth2622K07P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P119Input : RatPair2542 := (momentPanelPhase2622K07P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P119Expected : RatState2542 :=
  ((((30985382401828599570423936620791268249519831191632083369277722353323005416147362207 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((78559560579070237954359916895944567 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P119_replay :
    compactExp2620 momentScalarAmp2622K07P119Input 20 = momentScalarAmp2622K07P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K07P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P119_replay] at h
  simpa only [momentPanelPhase_owner2622K07P119] using h

theorem momentScalarAmp2622K07P119_radius_le :
    (momentScalarAmp2622K07P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P119Expected]

def momentScalarGrow2622K07P119Input : RatPair2542 := (momentPanelGrowth2622K07P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P119Expected : RatState2542 :=
  ((((719452727394665475856604617654617422493944870959918824722879905104485189898376606700503545626675 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((456007211219932913950997636604350983367286632387 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P119_replay :
    compactExp2620 momentScalarGrow2622K07P119Input 20 = momentScalarGrow2622K07P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P119] using h

theorem momentScalarGrow2622K07P119_radius_le :
    (momentScalarGrow2622K07P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P119Expected]

end ConnesWeilRH.Dev
