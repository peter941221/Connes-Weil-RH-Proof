import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P163 : ℚ := ((-2391426455657181430147856559359143311987 : ℚ) / 37301379502075787076681389840112025600)

def momentPanelGrowth2622K08P163 : ℚ := ((944758576007765529747837127177338591803 : ℚ) / 432407789183611239852779831704525209600)

theorem momentPanelPhase_owner2622K08P163 :
    (momentPanelPhase2622K08P163 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P163 :
    (momentPanelGrowth2622K08P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P163Input : RatPair2542 := (momentPanelPhase2622K08P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P163Expected : RatState2542 :=
  ((((299413747822493556233466817007354667800268540513320057231864183557 : ℚ) / 2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024), 0), ((604560081064679793384361 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K08P163_replay :
    compactExp2620 momentScalarAmp2622K08P163Input 20 = momentScalarAmp2622K08P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K08P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P163_replay] at h
  simpa only [momentPanelPhase_owner2622K08P163] using h

theorem momentScalarAmp2622K08P163_radius_le :
    (momentScalarAmp2622K08P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P163Expected]

def momentScalarGrow2622K08P163Input : RatPair2542 := (momentPanelGrowth2622K08P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P163Expected : RatState2542 :=
  ((((18988007004429816045919285846938909065959533666528826297273572540955439654443624653487460698564477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12035054161131853986947798413346942622189103404405 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K08P163_replay :
    compactExp2620 momentScalarGrow2622K08P163Input 20 = momentScalarGrow2622K08P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P163] using h

theorem momentScalarGrow2622K08P163_radius_le :
    (momentScalarGrow2622K08P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P163Expected]

end ConnesWeilRH.Dev
