import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K23
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K23P047 : ℚ := ((-6607056132588751650501555951009446301 : ℚ) / 177268259935915599505298976239779840)

def momentPanelGrowth2622K23P047 : ℚ := ((9069280857101648275995212159826149427523 : ℚ) / 22458982924291703410236951044810185113600)

theorem momentPanelPhase_owner2622K23P047 :
    (momentPanelPhase2622K23P047 : ℝ) = momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-17 / 40) 0 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P047, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K23P047 :
    (momentPanelGrowth2622K23P047 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2))
      (-17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P047, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K23P047Input : RatPair2542 := (momentPanelPhase2622K23P047 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K23P047Expected : RatState2542 :=
  ((((138926944306231290663051741851693763471572641607118834708334614743288078184505283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22014635838200014166715454490947 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K23P047_replay :
    compactExp2620 momentScalarAmp2622K23P047Input 20 = momentScalarAmp2622K23P047Expected := by
  decide +kernel

theorem momentScalarAmp2622K23P047_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-17 / 40) 0) -
      (momentScalarAmp2622K23P047Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K23P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K23P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P047]
  have h := compactExp_real_error2620 momentPanelPhase2622K23P047 20 hsmall
  change |Real.exp (momentPanelPhase2622K23P047 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K23P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K23P047Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K23P047_replay] at h
  simpa only [momentPanelPhase_owner2622K23P047] using h

theorem momentScalarAmp2622K23P047_radius_le :
    (momentScalarAmp2622K23P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarAmp2622K23P047Expected]

def momentScalarGrow2622K23P047Input : RatPair2542 := (momentPanelGrowth2622K23P047 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K23P047Expected : RatState2542 :=
  ((((3198698948799018079643625078609174858202656695597234832876047522331669911231101953389063916825701 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2027415540422584598377872155170412557687855412589 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K23P047_replay :
    compactExp2620 momentScalarGrow2622K23P047Input 20 = momentScalarGrow2622K23P047Expected := by
  decide +kernel

theorem momentScalarGrow2622K23P047_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K23P047Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K23P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K23P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P047]
  have h := compactExp_real_error2620 momentPanelGrowth2622K23P047 20 hsmall
  change |Real.exp (momentPanelGrowth2622K23P047 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K23P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K23P047Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K23P047_replay] at h
  simpa only [momentPanelGrowth_owner2622K23P047] using h

theorem momentScalarGrow2622K23P047_radius_le :
    (momentScalarGrow2622K23P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarGrow2622K23P047Expected]

end ConnesWeilRH.Dev
