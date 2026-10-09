import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P121 : ℚ := ((-329293753002466550328691094016685800608900127473420913 : ℚ) / 10285032323177688094882220353046951851801348721868800)

def momentPanelGrowth2622K02P121 : ℚ := ((4180275492911819300889197888813196574650148468170853 : ℚ) / 14972827369870413324218160619703818627250480008396800)

theorem momentPanelPhase_owner2622K02P121 :
    (momentPanelPhase2622K02P121 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (63 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P121, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P121 :
    (momentPanelGrowth2622K02P121 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P121, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P121Input : RatPair2542 := (momentPanelPhase2622K02P121 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P121Expected : RatState2542 :=
  ((((26600021956584447501887200394184732246281801122495550930720737068753312073152289471 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16860281698009257786365124268254379 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P121_replay :
    compactExp2620 momentScalarAmp2622K02P121Input 20 = momentScalarAmp2622K02P121Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P121_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (63 / 200) 0) -
      (momentScalarAmp2622K02P121Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P121]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P121 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P121 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P121Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P121_replay] at h
  simpa only [momentPanelPhase_owner2622K02P121] using h

theorem momentScalarAmp2622K02P121_radius_le :
    (momentScalarAmp2622K02P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P121Expected]

def momentScalarGrow2622K02P121Input : RatPair2542 := (momentPanelGrowth2622K02P121 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P121Expected : RatState2542 :=
  ((((2823902069673253289400899840863869962469379399869984026644256220476837008581966308820893641872553 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1789860100240522744934511407815883448482815534719 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P121_replay :
    compactExp2620 momentScalarGrow2622K02P121Input 20 = momentScalarGrow2622K02P121Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P121_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P121Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P121]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P121 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P121 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P121Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P121_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P121] using h

theorem momentScalarGrow2622K02P121_radius_le :
    (momentScalarGrow2622K02P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P121Expected]

end ConnesWeilRH.Dev
