import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P165 : ℚ := ((-29616707837027819548020435922122075775 : ℚ) / 465116217030940106161958366490918912)

def momentPanelGrowth2622K07P165 : ℚ := ((38822217165673626030277019876305225 : ℚ) / 14725029372251112727785704433647616)

theorem momentPanelPhase_owner2622K07P165 :
    (momentPanelPhase2622K07P165 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (151 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P165, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P165 :
    (momentPanelGrowth2622K07P165 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P165, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P165Input : RatPair2542 := (momentPanelPhase2622K07P165 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P165Expected : RatState2542 :=
  ((((473689147050453165533760265387358526229400902599734565051632767575969 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2418452148026360117081359 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P165_replay :
    compactExp2620 momentScalarAmp2622K07P165Input 20 = momentScalarAmp2622K07P165Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P165_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (151 / 200) 0) -
      (momentScalarAmp2622K07P165Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P165]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P165 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P165 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P165Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P165_replay] at h
  simpa only [momentPanelPhase_owner2622K07P165] using h

theorem momentScalarAmp2622K07P165_radius_le :
    (momentScalarAmp2622K07P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P165Expected]

def momentScalarGrow2622K07P165Input : RatPair2542 := (momentPanelGrowth2622K07P165 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P165Expected : RatState2542 :=
  ((((466043569840293624544232509583586901391442955630286094374701618183981694983334840950646132159539 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((37809851239600547906943294047715376505322669180893 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P165_replay :
    compactExp2620 momentScalarGrow2622K07P165Input 20 = momentScalarGrow2622K07P165Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P165_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P165Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P165]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P165 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P165 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P165Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P165_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P165] using h

theorem momentScalarGrow2622K07P165_radius_le :
    (momentScalarGrow2622K07P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P165Expected]

end ConnesWeilRH.Dev
