import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P179 : ℚ := ((-804500148916615367843021155057193668057 : ℚ) / 5380923267848788163473205766180044800)

def momentPanelGrowth2622K05P179 : ℚ := ((5481416960812048534782101886110253129 : ℚ) / 366097493345912651152247885712588800)

theorem momentPanelPhase_owner2622K05P179 :
    (momentPanelPhase2622K05P179 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (179 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P179, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P179 :
    (momentPanelGrowth2622K05P179 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P179, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P179Input : RatPair2542 := (momentPanelPhase2622K05P179 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P179Expected : RatState2542 :=
  ((((25024587708890886682463829614903 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P179_replay :
    compactExp2620 momentScalarAmp2622K05P179Input 20 = momentScalarAmp2622K05P179Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P179_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (179 / 200) 0) -
      (momentScalarAmp2622K05P179Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P179]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P179 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P179 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P179Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P179_replay] at h
  simpa only [momentPanelPhase_owner2622K05P179] using h

theorem momentScalarAmp2622K05P179_radius_le :
    (momentScalarAmp2622K05P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P179Expected]

def momentScalarGrow2622K05P179Input : RatPair2542 := (momentPanelGrowth2622K05P179 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P179Expected : RatState2542 :=
  ((((6793586784596983559218128317990781794394438305769612870831160502731731741179754825756266872713906578693 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8611771397294739418377731649281129126593647874772773607 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P179_replay :
    compactExp2620 momentScalarGrow2622K05P179Input 20 = momentScalarGrow2622K05P179Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P179_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P179Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P179]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P179 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P179 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P179Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P179_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P179] using h

theorem momentScalarGrow2622K05P179_radius_le :
    (momentScalarGrow2622K05P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P179Expected]

end ConnesWeilRH.Dev
