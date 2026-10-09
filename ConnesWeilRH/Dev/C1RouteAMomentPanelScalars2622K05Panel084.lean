import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P084 : ℚ := ((-813389020718464206745194135645675456847 : ℚ) / 26961407086134165494553081134501068800)

def momentPanelGrowth2622K05P084 : ℚ := ((316979686536175551167080774071183673209 : ℚ) / 6292699723291825538294851697854172364800)

theorem momentPanelPhase_owner2622K05P084 :
    (momentPanelPhase2622K05P084 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P084 :
    (momentPanelGrowth2622K05P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P084Input : RatPair2542 := (momentPanelPhase2622K05P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P084Expected : RatState2542 :=
  ((((168858974302657362049289169139426880440780680314855584204813729691447978260153009545 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((214060338785020791876804786344530133 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P084_replay :
    compactExp2620 momentScalarAmp2622K05P084Input 20 = momentScalarAmp2622K05P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K05P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P084_replay] at h
  simpa only [momentPanelPhase_owner2622K05P084] using h

theorem momentScalarAmp2622K05P084_radius_le :
    (momentScalarAmp2622K05P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P084Expected]

def momentScalarGrow2622K05P084Input : RatPair2542 := (momentPanelGrowth2622K05P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P084Expected : RatState2542 :=
  ((((2246338277264540474898739195345266448518710768166573283129708887711243710460893276775864990636453 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2847571928695356710810995521464562961868481869427 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P084_replay :
    compactExp2620 momentScalarGrow2622K05P084Input 20 = momentScalarGrow2622K05P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P084] using h

theorem momentScalarGrow2622K05P084_radius_le :
    (momentScalarGrow2622K05P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P084Expected]

end ConnesWeilRH.Dev
