import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P106 : ℚ := ((-93150206813248914997176396088061617275 : ℚ) / 3156835360350760591464845979160674304)

def momentPanelGrowth2622K07P106 : ℚ := ((240869692199575973745597435355513930025 : ℚ) / 1275135093325711319006525676362057908224)

theorem momentPanelPhase_owner2622K07P106 :
    (momentPanelPhase2622K07P106 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P106 :
    (momentPanelGrowth2622K07P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P106Input : RatPair2542 := (momentPanelPhase2622K07P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P106Expected : RatState2542 :=
  ((((327091814472788976139194762284263814323386478207662077738214096181950061815527072365 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((414649803241712454831148443995856067 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P106_replay :
    compactExp2620 momentScalarAmp2622K07P106Input 20 = momentScalarAmp2622K07P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K07P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P106_replay] at h
  simpa only [momentPanelPhase_owner2622K07P106] using h

theorem momentScalarAmp2622K07P106_radius_le :
    (momentScalarAmp2622K07P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P106Expected]

def momentScalarGrow2622K07P106Input : RatPair2542 := (momentPanelGrowth2622K07P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P106Expected : RatState2542 :=
  ((((2580095058601494244874686797092267911380679433064412977765362318717325798359034320653589384565485 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3270658460484050659238322502774989397267394838185 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P106_replay :
    compactExp2620 momentScalarGrow2622K07P106Input 20 = momentScalarGrow2622K07P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P106] using h

theorem momentScalarGrow2622K07P106_radius_le :
    (momentScalarGrow2622K07P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P106Expected]

end ConnesWeilRH.Dev
