import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P104 : ℚ := ((-111970965724599494365621313969221622590716826837524377 : ℚ) / 3725972826578178865490761351844852003040798336614400)

def momentPanelGrowth2622K02P104 : ℚ := ((2947332165504076629469944161255823051828472299503199 : ℚ) / 21819905450857985257607181729540826594533068662374400)

theorem momentPanelPhase_owner2622K02P104 :
    (momentPanelPhase2622K02P104 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P104 :
    (momentPanelGrowth2622K02P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P104Input : RatPair2542 := (momentPanelPhase2622K02P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P104Expected : RatState2542 :=
  ((((94924961046724808859202822619508766888126109976863457103723924062668882859483310493 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((120335132521951270494479792194626559 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P104_replay :
    compactExp2620 momentScalarAmp2622K02P104Input 20 = momentScalarAmp2622K02P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K02P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P104_replay] at h
  simpa only [momentPanelPhase_owner2622K02P104] using h

theorem momentScalarAmp2622K02P104_radius_le :
    (momentScalarAmp2622K02P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P104Expected]

def momentScalarGrow2622K02P104Input : RatPair2542 := (momentPanelGrowth2622K02P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P104Expected : RatState2542 :=
  ((((152806252462027362761914292991451678733227641729904164207101089147548641461119923478747680944549 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1549639301595587441955443967649602413546508186875 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P104_replay :
    compactExp2620 momentScalarGrow2622K02P104Input 20 = momentScalarGrow2622K02P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P104] using h

theorem momentScalarGrow2622K02P104_radius_le :
    (momentScalarGrow2622K02P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P104Expected]

end ConnesWeilRH.Dev
