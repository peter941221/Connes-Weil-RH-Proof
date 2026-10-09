import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P030 : ℚ := ((-21024947 : ℚ) / 430650)

def momentPanelGrowth2622K06P030 : ℚ := ((5881 : ℚ) / 6400)

theorem momentPanelPhase_owner2622K06P030 :
    (momentPanelPhase2622K06P030 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P030 :
    (momentPanelGrowth2622K06P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P030Input : RatPair2542 := (momentPanelPhase2622K06P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P030Expected : RatState2542 :=
  ((((1338821906298851182104411999890499693431266678941207012026630354041803939575 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((849827632925305699616129599 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P030_replay :
    compactExp2620 momentScalarAmp2622K06P030Input 20 = momentScalarAmp2622K06P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K06P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P030_replay] at h
  simpa only [momentPanelPhase_owner2622K06P030] using h

theorem momentScalarAmp2622K06P030_radius_le :
    (momentScalarAmp2622K06P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P030Expected]

def momentScalarGrow2622K06P030Input : RatPair2542 := (momentPanelGrowth2622K06P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P030Expected : RatState2542 :=
  ((((167311020404541361915097542299011227319887244444918060168696120888927112696691885485803170385551 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((6786935346452527042496622657105100912820747201837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P030_replay :
    compactExp2620 momentScalarGrow2622K06P030Input 20 = momentScalarGrow2622K06P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P030] using h

theorem momentScalarGrow2622K06P030_radius_le :
    (momentScalarGrow2622K06P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P030Expected]

end ConnesWeilRH.Dev
