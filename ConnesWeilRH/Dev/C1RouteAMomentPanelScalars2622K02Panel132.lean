import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P132 : ℚ := ((-870088614707409225119824158709256296355778744582709 : ℚ) / 24948289668500178720898838745977174983970410987520)

def momentPanelGrowth2622K02P132 : ℚ := ((1356661532461770541894335803011146052181526926866974293 : ℚ) / 3160820847780014001720504364178236230553372092845260800)

theorem momentPanelPhase_owner2622K02P132 :
    (momentPanelPhase2622K02P132 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P132 :
    (momentPanelGrowth2622K02P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P132Input : RatPair2542 := (momentPanelPhase2622K02P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P132Expected : RatState2542 :=
  ((((381261027965425622421040688779415487856601347101460578209131285286540055868566485 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((966643693172169680571091914897533 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P132_replay :
    compactExp2620 momentScalarAmp2622K02P132Input 20 = momentScalarAmp2622K02P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K02P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P132_replay] at h
  simpa only [momentPanelPhase_owner2622K02P132] using h

theorem momentScalarAmp2622K02P132_radius_le :
    (momentScalarAmp2622K02P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P132Expected]

def momentScalarGrow2622K02P132Input : RatPair2542 := (momentPanelGrowth2622K02P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P132Expected : RatState2542 :=
  ((((1640487490662595360040437695214484518997167682554920145740673575480015346335967554694855830929711 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((519891025245209211484189584142606491176131547143 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P132_replay :
    compactExp2620 momentScalarGrow2622K02P132Input 20 = momentScalarGrow2622K02P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P132] using h

theorem momentScalarGrow2622K02P132_radius_le :
    (momentScalarGrow2622K02P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P132Expected]

end ConnesWeilRH.Dev
