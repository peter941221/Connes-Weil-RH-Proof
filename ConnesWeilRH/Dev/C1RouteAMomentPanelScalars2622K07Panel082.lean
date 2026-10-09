import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P082 : ℚ := ((-3972381503177745617525547319457551875 : ℚ) / 129077254717639230578000307184205824)

def momentPanelGrowth2622K07P082 : ℚ := ((674526846776519566556380136156623025 : ℚ) / 5214485814641222555974294622126997504)

theorem momentPanelPhase_owner2622K07P082 :
    (momentPanelPhase2622K07P082 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P082, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P082 :
    (momentPanelGrowth2622K07P082 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P082, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P082Input : RatPair2542 := (momentPanelPhase2622K07P082 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P082Expected : RatState2542 :=
  ((((23015923379551019767811856319528134655331319827389605469984657445165181630304534171 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((116708021626628988882805099159518215 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P082_replay :
    compactExp2620 momentScalarAmp2622K07P082Input 20 = momentScalarAmp2622K07P082Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P082_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 40) 0) -
      (momentScalarAmp2622K07P082Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P082]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P082 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P082 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P082Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P082_replay] at h
  simpa only [momentPanelPhase_owner2622K07P082] using h

theorem momentScalarAmp2622K07P082_radius_le :
    (momentScalarAmp2622K07P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P082Expected]

def momentScalarGrow2622K07P082Input : RatPair2542 := (momentPanelGrowth2622K07P082 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P082Expected : RatState2542 :=
  ((((2430957470993444212063229179434100322630293104059747250928920894776869916855316444007008616259887 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3081604317075610767448017361875733812662790074839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P082_replay :
    compactExp2620 momentScalarGrow2622K07P082Input 20 = momentScalarGrow2622K07P082Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P082_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P082Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P082]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P082 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P082 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P082Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P082_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P082] using h

theorem momentScalarGrow2622K07P082_radius_le :
    (momentScalarGrow2622K07P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P082Expected]

end ConnesWeilRH.Dev
