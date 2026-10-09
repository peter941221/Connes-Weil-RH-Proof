import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P166 : ℚ := ((-85466205604323789322516641018937284489588030973342521 : ℚ) / 1183973323484229019331901125956828690386307461939200)

def momentPanelGrowth2622K01P166 : ℚ := ((549857406126782800252407819128223056550206045489798731 : ℚ) / 197115287736427283776117473011760252704765429101363200)

theorem momentPanelPhase_owner2622K01P166 :
    (momentPanelPhase2622K01P166 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (153 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P166 :
    (momentPanelGrowth2622K01P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P166Input : RatPair2542 := (momentPanelPhase2622K01P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P166Expected : RatState2542 :=
  ((((1490977811054942211705154189883096630582046083263624207676424483 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((302231470025009704501813 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P166_replay :
    compactExp2620 momentScalarAmp2622K01P166Input 20 = momentScalarAmp2622K01P166Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622K01P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P166]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P166 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P166_replay] at h
  simpa only [momentPanelPhase_owner2622K01P166] using h

theorem momentScalarAmp2622K01P166_radius_le :
    (momentScalarAmp2622K01P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P166Expected]

def momentScalarGrow2622K01P166Input : RatPair2542 := (momentPanelGrowth2622K01P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P166Expected : RatState2542 :=
  ((((2172463984019495488204798756404819813639224512888784159731470877995122869087090721783879965620347 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((22031343576573078967025276147906806877785969088863 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P166_replay :
    compactExp2620 momentScalarGrow2622K01P166Input 20 = momentScalarGrow2622K01P166Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P166_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P166] using h

theorem momentScalarGrow2622K01P166_radius_le :
    (momentScalarGrow2622K01P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P166Expected]

end ConnesWeilRH.Dev
