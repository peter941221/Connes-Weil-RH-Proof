import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P013 : ℚ := ((-85803517520391396404477675315002131876341563906657479 : ℚ) / 1183973323484229019331901125956828690386307461939200)

def momentPanelGrowth2622K01P013 : ℚ := ((549857406126782800252407819128223056550206045489798731 : ℚ) / 197115287736427283776117473011760252704765429101363200)

theorem momentPanelPhase_owner2622K01P013 :
    (momentPanelPhase2622K01P013 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P013 :
    (momentPanelGrowth2622K01P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P013Input : RatPair2542 := (momentPanelPhase2622K01P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P013Expected : RatState2542 :=
  ((((71766442856045975975075649552724636212160020440962866687003426573 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925865105160703142335 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P013_replay :
    compactExp2620 momentScalarAmp2622K01P013Input 20 = momentScalarAmp2622K01P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K01P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P013_replay] at h
  simpa only [momentPanelPhase_owner2622K01P013] using h

theorem momentScalarAmp2622K01P013_radius_le :
    (momentScalarAmp2622K01P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P013Expected]

def momentScalarGrow2622K01P013Input : RatPair2542 := (momentPanelGrowth2622K01P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P013Expected : RatState2542 :=
  ((((2172463984019495488204798756404819813639224512888784159731470877995122869087090721783879965620347 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((22031343576573078967025276147906806877785969088863 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P013_replay :
    compactExp2620 momentScalarGrow2622K01P013Input 20 = momentScalarGrow2622K01P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P013] using h

theorem momentScalarGrow2622K01P013_radius_le :
    (momentScalarGrow2622K01P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P013Expected]

end ConnesWeilRH.Dev
