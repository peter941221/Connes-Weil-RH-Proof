import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P100 : ℚ := ((-2422000223791429182369295277535046865229 : ℚ) / 80235184151085643030092931362350694400)

def momentPanelGrowth2622K05P100 : ℚ := ((2696632751011044712713424702923148434683 : ℚ) / 32990908064722284401257496536591997337600)

theorem momentPanelPhase_owner2622K05P100 :
    (momentPanelPhase2622K05P100 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P100 :
    (momentPanelGrowth2622K05P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P100Input : RatPair2542 := (momentPanelPhase2622K05P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P100Expected : RatState2542 :=
  ((((10369360526566327374948278862691489337307173680852423098579725845575537582366524137 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((210321672154293583477641477860737951 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P100_replay :
    compactExp2620 momentScalarAmp2622K05P100Input 20 = momentScalarAmp2622K05P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K05P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P100_replay] at h
  simpa only [momentPanelPhase_owner2622K05P100] using h

theorem momentScalarAmp2622K05P100_radius_le :
    (momentScalarAmp2622K05P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P100Expected]

def momentScalarGrow2622K05P100Input : RatPair2542 := (momentPanelGrowth2622K05P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P100Expected : RatState2542 :=
  ((((2317913704521693092719571942129493611424606886305900390689498121174066343506349004361704721708809 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2938304469767254417176494409006544211769049518637 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P100_replay :
    compactExp2620 momentScalarGrow2622K05P100Input 20 = momentScalarGrow2622K05P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P100] using h

theorem momentScalarGrow2622K05P100_radius_le :
    (momentScalarGrow2622K05P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P100Expected]

end ConnesWeilRH.Dev
