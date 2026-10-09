import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P105 : ℚ := ((-31130693903082634422602528213550426775 : ℚ) / 1055739984689276748907302323939704832)

def momentPanelGrowth2622K07P105 : ℚ := ((911943763904042903845112717021934025 : ℚ) / 5014906904141290119002653669472600064)

theorem momentPanelPhase_owner2622K07P105 :
    (momentPanelPhase2622K07P105 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P105 :
    (momentPanelGrowth2622K07P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P105Input : RatPair2542 := (momentPanelPhase2622K07P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P105Expected : RatState2542 :=
  ((((333826357382264058071660184027773427893862530534343933502246935444037985190103882451 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((211593541309193475827271015987962225 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P105_replay :
    compactExp2620 momentScalarAmp2622K07P105Input 20 = momentScalarAmp2622K07P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K07P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P105_replay] at h
  simpa only [momentPanelPhase_owner2622K07P105] using h

theorem momentScalarAmp2622K07P105_radius_le :
    (momentScalarAmp2622K07P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P105Expected]

def momentScalarGrow2622K07P105Input : RatPair2542 := (momentPanelGrowth2622K07P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P105Expected : RatState2542 :=
  ((((20015369744303144770852874722340905378359112812858731118484476773790846559749213626278171052509 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((3247678856959534793403239281148612415552375996609 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P105_replay :
    compactExp2620 momentScalarGrow2622K07P105Input 20 = momentScalarGrow2622K07P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P105] using h

theorem momentScalarGrow2622K07P105_radius_le :
    (momentScalarGrow2622K07P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P105Expected]

end ConnesWeilRH.Dev
