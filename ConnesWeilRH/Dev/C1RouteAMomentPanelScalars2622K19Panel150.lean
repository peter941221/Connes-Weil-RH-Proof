import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P150 : ℚ := ((-795231369247591850222226466914245837003 : ℚ) / 17144720837966757009362611512069324800)

def momentPanelGrowth2622K19P150 : ℚ := ((12578686450849990899878469861777530033443 : ℚ) / 13327517602174062958649115359825205657600)

theorem momentPanelPhase_owner2622K19P150 :
    (momentPanelPhase2622K19P150 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P150 :
    (momentPanelGrowth2622K19P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P150Input : RatPair2542 := (momentPanelPhase2622K19P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P150Expected : RatState2542 :=
  ((((15329236200524169512676001257185551934113494832731363842168459228836735158159 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19435392915253956809514814021 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K19P150_replay :
    compactExp2620 momentScalarAmp2622K19P150Input 20 = momentScalarAmp2622K19P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K19P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P150_replay] at h
  simpa only [momentPanelPhase_owner2622K19P150] using h

theorem momentScalarAmp2622K19P150_radius_le :
    (momentScalarAmp2622K19P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P150Expected]

def momentScalarGrow2622K19P150Input : RatPair2542 := (momentPanelGrowth2622K19P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P150Expected : RatState2542 :=
  ((((5488977595422274813922538949925240234499178216596221522268969865957762037671723547513334849110891 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3479049740277610166567570022950308516351703159513 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K19P150_replay :
    compactExp2620 momentScalarGrow2622K19P150Input 20 = momentScalarGrow2622K19P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P150] using h

theorem momentScalarGrow2622K19P150_radius_le :
    (momentScalarGrow2622K19P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P150Expected]

end ConnesWeilRH.Dev
