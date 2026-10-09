import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P096 : ℚ := ((-19827399 : ℚ) / 663850)

def momentPanelGrowth2622K06P096 : ℚ := ((68007467 : ℚ) / 825186675)

theorem momentPanelPhase_owner2622K06P096 :
    (momentPanelPhase2622K06P096 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P096, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P096 :
    (momentPanelGrowth2622K06P096 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P096, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P096Input : RatPair2542 := (momentPanelPhase2622K06P096 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P096Expected : RatState2542 :=
  ((((7132640860013114197562077267356999534950652509432599963179502176661729192214103343 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((289342528377826721889129788426657217 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P096_replay :
    compactExp2620 momentScalarAmp2622K06P096Input 20 = momentScalarAmp2622K06P096Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P096_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 200) 0) -
      (momentScalarAmp2622K06P096Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P096]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P096 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P096 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P096Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P096_replay] at h
  simpa only [momentPanelPhase_owner2622K06P096] using h

theorem momentScalarAmp2622K06P096_radius_le :
    (momentScalarAmp2622K06P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P096Expected]

def momentScalarGrow2622K06P096Input : RatPair2542 := (momentPanelGrowth2622K06P096 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P096Expected : RatState2542 :=
  ((((2319481100074880709381864972562386629809388086665642850832815548277210347843163031048075779962865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1470145688815329354633664756375959333216878584029 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P096_replay :
    compactExp2620 momentScalarGrow2622K06P096Input 20 = momentScalarGrow2622K06P096Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P096_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P096Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P096]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P096 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P096 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P096Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P096_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P096] using h

theorem momentScalarGrow2622K06P096_radius_le :
    (momentScalarGrow2622K06P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P096Expected]

end ConnesWeilRH.Dev
