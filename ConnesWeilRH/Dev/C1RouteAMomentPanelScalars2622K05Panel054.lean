import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P054 : ℚ := ((-823136997951339733028503217769676818307 : ℚ) / 23635091911135291545025731923594444800)

def momentPanelGrowth2622K05P054 : ℚ := ((87696909166284452133041099075774721 : ℚ) / 293080818772766637626037781082931200)

theorem momentPanelPhase_owner2622K05P054 :
    (momentPanelPhase2622K05P054 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P054 :
    (momentPanelGrowth2622K05P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P054Input : RatPair2542 := (momentPanelPhase2622K05P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P054Expected : RatState2542 :=
  ((((1601282053888097942520398004066456823066844933324660351839440745472509184066323397 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2029933579284977923807934595348989 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P054_replay :
    compactExp2620 momentScalarAmp2622K05P054Input 20 = momentScalarAmp2622K05P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K05P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P054_replay] at h
  simpa only [momentPanelPhase_owner2622K05P054] using h

theorem momentScalarAmp2622K05P054_radius_le :
    (momentScalarAmp2622K05P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P054Expected]

def momentScalarGrow2622K05P054Input : RatPair2542 := (momentPanelGrowth2622K05P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P054Expected : RatState2542 :=
  ((((2881045281709214139916397964432890900071303158812460953434269332195650998905430951062616161628049 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3652157738454198456492072446109540595968949795797 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P054_replay :
    compactExp2620 momentScalarGrow2622K05P054Input 20 = momentScalarGrow2622K05P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P054] using h

theorem momentScalarGrow2622K05P054_radius_le :
    (momentScalarGrow2622K05P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P054Expected]

end ConnesWeilRH.Dev
