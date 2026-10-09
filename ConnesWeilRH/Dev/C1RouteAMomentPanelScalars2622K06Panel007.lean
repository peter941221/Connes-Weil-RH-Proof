import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P007 : ℚ := ((-496863 : ℚ) / 5110)

def momentPanelGrowth2622K06P007 : ℚ := ((418226107 : ℚ) / 80652675)

theorem momentPanelPhase_owner2622K06P007 :
    (momentPanelPhase2622K06P007 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P007, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P007 :
    (momentPanelGrowth2622K06P007 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P007, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P007Input : RatPair2542 := (momentPanelPhase2622K06P007 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P007Expected : RatState2542 :=
  ((((78980857878341647172599662871604204957072186920260633 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2417851639229258351018143 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P007_replay :
    compactExp2620 momentScalarAmp2622K06P007Input 20 = momentScalarAmp2622K06P007Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P007_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 40) 0) -
      (momentScalarAmp2622K06P007Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P007]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P007 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P007 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P007Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P007_replay] at h
  simpa only [momentPanelPhase_owner2622K06P007] using h

theorem momentScalarAmp2622K06P007_radius_le :
    (momentScalarAmp2622K06P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P007Expected]

def momentScalarGrow2622K06P007Input : RatPair2542 := (momentPanelGrowth2622K06P007 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P007Expected : RatState2542 :=
  ((((381629195053244656208691208723148976619056946628115514909632825367908813811460661860137870468273863 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((241885042890401221549597645664608908077925305881329 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P007_replay :
    compactExp2620 momentScalarGrow2622K06P007Input 20 = momentScalarGrow2622K06P007Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P007_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P007Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P007]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P007 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P007 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P007Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P007_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P007] using h

theorem momentScalarGrow2622K06P007_radius_le :
    (momentScalarGrow2622K06P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P007Expected]

end ConnesWeilRH.Dev
