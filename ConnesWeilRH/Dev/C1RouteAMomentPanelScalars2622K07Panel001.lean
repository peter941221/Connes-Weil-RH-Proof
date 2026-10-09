import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P001 : ℚ := ((-102381991321722770264369956730631009525 : ℚ) / 703475094693054536984186463604178944)

def momentPanelGrowth2622K07P001 : ℚ := ((726772287736478389750023066701522638025 : ℚ) / 58443641578464666416581460897147387904)

theorem momentPanelPhase_owner2622K07P001 :
    (momentPanelPhase2622K07P001 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-177 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P001, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P001 :
    (momentPanelGrowth2622K07P001 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P001, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P001Input : RatPair2542 := (momentPanelPhase2622K07P001 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P001Expected : RatState2542 :=
  ((((1328846695741129120266097568647721 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P001_replay :
    compactExp2620 momentScalarAmp2622K07P001Input 20 = momentScalarAmp2622K07P001Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P001_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-177 / 200) 0) -
      (momentScalarAmp2622K07P001Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P001]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P001 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P001 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P001Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P001_replay] at h
  simpa only [momentPanelPhase_owner2622K07P001] using h

theorem momentScalarAmp2622K07P001_radius_le :
    (momentScalarAmp2622K07P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P001Expected]

def momentScalarGrow2622K07P001Input : RatPair2542 := (momentPanelGrowth2622K07P001 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P001Expected : RatState2542 :=
  ((((537329597678914537497869655792791676881234957017737313643453451731545098901625779499458283879337248397 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((681138109109528466897220205079145330722966148656095525 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P001_replay :
    compactExp2620 momentScalarGrow2622K07P001Input 20 = momentScalarGrow2622K07P001Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P001_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P001Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P001]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P001 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P001 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P001Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P001_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P001] using h

theorem momentScalarGrow2622K07P001_radius_le :
    (momentScalarGrow2622K07P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P001Expected]

end ConnesWeilRH.Dev
