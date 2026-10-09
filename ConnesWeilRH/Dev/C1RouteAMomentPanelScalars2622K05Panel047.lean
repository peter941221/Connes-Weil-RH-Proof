import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P047 : ℚ := ((-6596689484747699295857358264388270181 : ℚ) / 177268259935915599505298976239779840)

def momentPanelGrowth2622K05P047 : ℚ := ((9038377296597822861144075806522219664763 : ℚ) / 22458982924291703410236951044810185113600)

theorem momentPanelPhase_owner2622K05P047 :
    (momentPanelPhase2622K05P047 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-17 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P047, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P047 :
    (momentPanelGrowth2622K05P047 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P047, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P047Input : RatPair2542 := (momentPanelPhase2622K05P047 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P047Expected : RatState2542 :=
  ((((147293650176091871349109563348000671725072593467363464640918912510976583454974417 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((46680878251897754496864056593317 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P047_replay :
    compactExp2620 momentScalarAmp2622K05P047Input 20 = momentScalarAmp2622K05P047Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P047_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-17 / 40) 0) -
      (momentScalarAmp2622K05P047Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P047]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P047 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P047 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P047Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P047_replay] at h
  simpa only [momentPanelPhase_owner2622K05P047] using h

theorem momentScalarAmp2622K05P047_radius_le :
    (momentScalarAmp2622K05P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P047Expected]

def momentScalarGrow2622K05P047Input : RatPair2542 := (momentPanelGrowth2622K05P047 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P047Expected : RatState2542 :=
  ((((3194300565826938125314292574009769701987369101706184456289660447528517935500966313472210734188641 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((126539233609107870976182814925531379531559798853 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P047_replay :
    compactExp2620 momentScalarGrow2622K05P047Input 20 = momentScalarGrow2622K05P047Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P047_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P047Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P047]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P047 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P047 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P047Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P047_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P047] using h

theorem momentScalarGrow2622K05P047_radius_le :
    (momentScalarGrow2622K05P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P047Expected]

end ConnesWeilRH.Dev
