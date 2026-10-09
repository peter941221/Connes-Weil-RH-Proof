import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K27
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K27P044 : ℚ := ((-826408473677059676767016028727767225767 : ℚ) / 21444591673940911139239428784704716800)

def momentPanelGrowth2622K27P044 : ℚ := ((603458617556194555810934354342203490443 : ℚ) / 1313232273450995983023961060553628057600)

theorem momentPanelPhase_owner2622K27P044 :
    (momentPanelPhase2622K27P044 : ℝ) = momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K27P044 :
    (momentPanelGrowth2622K27P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K27P044Input : RatPair2542 := (momentPanelPhase2622K27P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K27P044Expected : RatState2542 :=
  ((((39194733775697244721652953423355156074170576655931784822347656479210523008382059 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24843528131501879639323650399559 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K27P044_replay :
    compactExp2620 momentScalarAmp2622K27P044Input 20 = momentScalarAmp2622K27P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K27P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K27P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K27P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K27P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelPhase2622K27P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K27P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K27P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K27P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K27P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K27P044_replay] at h
  simpa only [momentPanelPhase_owner2622K27P044] using h

theorem momentScalarAmp2622K27P044_radius_le :
    (momentScalarAmp2622K27P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarAmp2622K27P044Expected]

def momentScalarGrow2622K27P044Input : RatPair2542 := (momentPanelGrowth2622K27P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K27P044Expected : RatState2542 :=
  ((((845485811020549522111569864962651309051163329678662864763288324599945671159353701458463305906085 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((133972515766761880698344941531379115145690648439 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K27P044_replay :
    compactExp2620 momentScalarGrow2622K27P044Input 20 = momentScalarGrow2622K27P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K27P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 27).re * (storedWidth 27 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K27P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K27P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K27P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentPanelGrowth2622K27P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K27P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K27P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K27P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K27P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K27P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K27P044] using h

theorem momentScalarGrow2622K27P044_radius_le :
    (momentScalarGrow2622K27P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, momentScalarGrow2622K27P044Expected]

end ConnesWeilRH.Dev
