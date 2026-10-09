import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P122 : ℚ := ((-1196531560878343198587115361409168625 : ℚ) / 38698837523767387168891355453718528)

def momentPanelGrowth2622K07P122 : ℚ := ((1063241086559363896475190376737146070075 : ℚ) / 3221086829354411706403983887569069801472)

theorem momentPanelPhase_owner2622K07P122 :
    (momentPanelPhase2622K07P122 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P122 :
    (momentPanelGrowth2622K07P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P122Input : RatPair2542 := (momentPanelPhase2622K07P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P122Expected : RatState2542 :=
  ((((19932547458283370050758236706466111874877385549600558561441632204911514869312336429 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((50536501633573252775586363045413785 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P122_replay :
    compactExp2620 momentScalarAmp2622K07P122Input 20 = momentScalarAmp2622K07P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K07P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P122_replay] at h
  simpa only [momentPanelPhase_owner2622K07P122] using h

theorem momentScalarAmp2622K07P122_radius_le :
    (momentScalarAmp2622K07P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P122Expected]

def momentScalarGrow2622K07P122Input : RatPair2542 := (momentPanelGrowth2622K07P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P122Expected : RatState2542 :=
  ((((2971350413720789783108038419430814754449057642069906263421394915192883273326182015037351716157239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((470829118714979798747076910050581717117803433985 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P122_replay :
    compactExp2620 momentScalarGrow2622K07P122Input 20 = momentScalarGrow2622K07P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P122] using h

theorem momentScalarGrow2622K07P122_radius_le :
    (momentScalarGrow2622K07P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P122Expected]

end ConnesWeilRH.Dev
