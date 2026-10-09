import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P042 : ℚ := ((-228880995200787963334311463979436743023153989634231 : ℚ) / 5894532970875614308770721053826414913260743557120)

def momentPanelGrowth2622K01P042 : ℚ := ((4029506046211685293849751398073483613550815077237553 : ℚ) / 8255236335803589601038152504445116106216216041881600)

theorem momentPanelPhase_owner2622K01P042 :
    (momentPanelPhase2622K01P042 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P042 :
    (momentPanelGrowth2622K01P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P042Input : RatPair2542 := (momentPanelPhase2622K01P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P042Expected : RatState2542 :=
  ((((7314050817464958817730082560453485834928750885499397792332392061415325663103435 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((37088019418338071857417169428187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P042_replay :
    compactExp2620 momentScalarAmp2622K01P042Input 20 = momentScalarAmp2622K01P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K01P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P042_replay] at h
  simpa only [momentPanelPhase_owner2622K01P042] using h

theorem momentScalarAmp2622K01P042_radius_le :
    (momentScalarAmp2622K01P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P042Expected]

def momentScalarGrow2622K01P042Input : RatPair2542 := (momentPanelGrowth2622K01P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P042Expected : RatState2542 :=
  ((((3480040796186607025648475290301023563210958634520894395147171403807994277948038352666828584302709 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2205736875275195977620049047929892133774143461173 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P042_replay :
    compactExp2620 momentScalarGrow2622K01P042Input 20 = momentScalarGrow2622K01P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P042] using h

theorem momentScalarGrow2622K01P042_radius_le :
    (momentScalarGrow2622K01P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P042Expected]

end ConnesWeilRH.Dev
