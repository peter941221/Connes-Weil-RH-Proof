import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P047 : ℚ := ((-1419725621624288586020639610048179875 : ℚ) / 35453651987183119901059795247955968)

def momentPanelGrowth2622K07P047 : ℚ := ((421387382997833319956915066379694272025 : ℚ) / 898359316971668136409478041792407404544)

theorem momentPanelPhase_owner2622K07P047 :
    (momentPanelPhase2622K07P047 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P047, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P047 :
    (momentPanelGrowth2622K07P047 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P047, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P047Input : RatPair2542 := (momentPanelPhase2622K07P047 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P047Expected : RatState2542 :=
  ((((8679016488136969209777022258919973378921291332170540964825730393681537876777969 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11002383045392597660225170068103 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P047_replay :
    compactExp2620 momentScalarAmp2622K07P047Input 20 = momentScalarAmp2622K07P047Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P047_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 40) 0) -
      (momentScalarAmp2622K07P047Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P047]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P047 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P047 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P047Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P047_replay] at h
  simpa only [momentPanelPhase_owner2622K07P047] using h

theorem momentScalarAmp2622K07P047_radius_le :
    (momentScalarAmp2622K07P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P047Expected]

def momentScalarGrow2622K07P047Input : RatPair2542 := (momentPanelGrowth2622K07P047 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P047Expected : RatState2542 :=
  ((((3414367107551837513269405536625585414476477148409327103800410292377627162726436749838060875850061 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4328222577127708081599610290475841354330966314615 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P047_replay :
    compactExp2620 momentScalarGrow2622K07P047Input 20 = momentScalarGrow2622K07P047Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P047_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P047Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P047]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P047 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P047 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P047Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P047_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P047] using h

theorem momentScalarGrow2622K07P047_radius_le :
    (momentScalarGrow2622K07P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P047Expected]

end ConnesWeilRH.Dev
