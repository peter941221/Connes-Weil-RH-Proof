import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P137 : ℚ := ((-227838266465119198604340046244401700619324930045769 : ℚ) / 5894532970875614308770721053826414913260743557120)

def momentPanelGrowth2622K01P137 : ℚ := ((4029506046211685293849751398073483613550815077237553 : ℚ) / 8255236335803589601038152504445116106216216041881600)

theorem momentPanelPhase_owner2622K01P137 :
    (momentPanelPhase2622K01P137 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P137, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P137 :
    (momentPanelGrowth2622K01P137 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P137, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P137Input : RatPair2542 := (momentPanelPhase2622K01P137 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P137Expected : RatState2542 :=
  ((((17458769075385605237065835230562617436348428032991194781629574695339958485831537 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((44264872268935771866187689372101 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P137_replay :
    compactExp2620 momentScalarAmp2622K01P137Input 20 = momentScalarAmp2622K01P137Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P137_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 40) 0) -
      (momentScalarAmp2622K01P137Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P137]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P137 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P137 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P137Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P137_replay] at h
  simpa only [momentPanelPhase_owner2622K01P137] using h

theorem momentScalarAmp2622K01P137_radius_le :
    (momentScalarAmp2622K01P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P137Expected]

def momentScalarGrow2622K01P137Input : RatPair2542 := (momentPanelGrowth2622K01P137 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P137Expected : RatState2542 :=
  ((((3480040796186607025648475290301023563210958634520894395147171403807994277948038352666828584302709 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2205736875275195977620049047929892133774143461173 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P137_replay :
    compactExp2620 momentScalarGrow2622K01P137Input 20 = momentScalarGrow2622K01P137Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P137_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P137Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P137Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P137 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P137]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P137 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P137 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P137Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P137Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P137_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P137] using h

theorem momentScalarGrow2622K01P137_radius_le :
    (momentScalarGrow2622K01P137Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P137Expected]

end ConnesWeilRH.Dev
