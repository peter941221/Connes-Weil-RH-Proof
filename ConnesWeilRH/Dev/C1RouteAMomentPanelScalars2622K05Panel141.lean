import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P141 : ℚ := ((-796855012190375479358056470987883359901 : ℚ) / 19870676688697541514341122084909875200)

def momentPanelGrowth2622K05P141 : ℚ := ((659227923906690303896576713137799387 : ℚ) / 1098292480037737953456743657137766400)

theorem momentPanelPhase_owner2622K05P141 :
    (momentPanelPhase2622K05P141 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (103 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P141 :
    (momentPanelGrowth2622K05P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P141Input : RatPair2542 := (momentPanelPhase2622K05P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P141Expected : RatState2542 :=
  ((((2048502449937741706687497532222724617818519140540769789670364118018410696540241 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5193770557675931569828450324181 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P141_replay :
    compactExp2620 momentScalarAmp2622K05P141Input 20 = momentScalarAmp2622K05P141Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622K05P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P141]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P141 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P141_replay] at h
  simpa only [momentPanelPhase_owner2622K05P141] using h

theorem momentScalarAmp2622K05P141_radius_le :
    (momentScalarAmp2622K05P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P141Expected]

def momentScalarGrow2622K05P141Input : RatPair2542 := (momentPanelGrowth2622K05P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P141Expected : RatState2542 :=
  ((((1946458398051477764104964231148283013873249504482982862329025520058058203360138602656695906622709 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2467427744194498146855270231650264479002045543471 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P141_replay :
    compactExp2620 momentScalarGrow2622K05P141Input 20 = momentScalarGrow2622K05P141Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P141_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P141] using h

theorem momentScalarGrow2622K05P141_radius_le :
    (momentScalarGrow2622K05P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P141Expected]

end ConnesWeilRH.Dev
