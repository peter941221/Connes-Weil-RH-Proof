import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P089 : ℚ := ((-114257616511064109529182121823500109192872892508594107 : ℚ) / 3805898697369712618830025366134023730678232147558400)

def momentPanelGrowth2622K02P089 : ℚ := ((223013653437640102102604915067464009584563301709265893 : ℚ) / 4756540858132985387138910409461549772834738128342220800)

theorem momentPanelPhase_owner2622K02P089 :
    (momentPanelPhase2622K02P089 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P089 :
    (momentPanelGrowth2622K02P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P089Input : RatPair2542 := (momentPanelPhase2622K02P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P089Expected : RatState2542 :=
  ((((195686323692257095219061204411674014168982803357361345965487992146033461104057891999 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((124034493954984096168119363202914827 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P089_replay :
    compactExp2620 momentScalarAmp2622K02P089Input 20 = momentScalarAmp2622K02P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K02P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P089_replay] at h
  simpa only [momentPanelPhase_owner2622K02P089] using h

theorem momentScalarAmp2622K02P089_radius_le :
    (momentScalarAmp2622K02P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P089Expected]

def momentScalarGrow2622K02P089Input : RatPair2542 := (momentPanelGrowth2622K02P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P089Expected : RatState2542 :=
  ((((2238519101728616149793824973013458760216498965155284388764478946401941680332686430147695911480957 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2837659956046446395919818011592732835132195483249 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P089_replay :
    compactExp2620 momentScalarGrow2622K02P089Input 20 = momentScalarGrow2622K02P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P089] using h

theorem momentScalarGrow2622K02P089_radius_le :
    (momentScalarGrow2622K02P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P089Expected]

end ConnesWeilRH.Dev
