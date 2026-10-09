import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P106 : ℚ := ((-218878025933698733679419521074132707652745929654729225 : ℚ) / 7108561276272845431277947565727911072228998897467392)

def momentPanelGrowth2622K03P106 : ℚ := ((319069209702585943016010828337813512900989834806281475 : ℚ) / 2871348965574358068662134893738364224709721819606679552)

theorem momentPanelPhase_owner2622K03P106 :
    (momentPanelPhase2622K03P106 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P106 :
    (momentPanelGrowth2622K03P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P106Input : RatPair2542 := (momentPanelPhase2622K03P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P106Expected : RatState2542 :=
  ((((90644221472387337587551741766974517387814472836437761674897627891936085836769694625 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57454287963175012215200368706298983 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P106_replay :
    compactExp2620 momentScalarAmp2622K03P106Input 20 = momentScalarAmp2622K03P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K03P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P106_replay] at h
  simpa only [momentPanelPhase_owner2622K03P106] using h

theorem momentScalarAmp2622K03P106_radius_le :
    (momentScalarAmp2622K03P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P106Expected]

def momentScalarGrow2622K03P106Input : RatPair2542 := (momentPanelGrowth2622K03P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P106Expected : RatState2542 :=
  ((((2387031545170781598175577140009895826231928466839329602364813580972021457365221402171973804078369 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3025921650330658201080510498891598295473628906899 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P106_replay :
    compactExp2620 momentScalarGrow2622K03P106Input 20 = momentScalarGrow2622K03P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P106] using h

theorem momentScalarGrow2622K03P106_radius_le :
    (momentScalarGrow2622K03P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P106Expected]

end ConnesWeilRH.Dev
