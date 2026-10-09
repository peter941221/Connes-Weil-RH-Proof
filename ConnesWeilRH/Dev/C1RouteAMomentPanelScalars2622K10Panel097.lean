import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P097 : ℚ := ((-19396145149965598722196811385341453763 : ℚ) / 645386273588196152890001535921029120)

def momentPanelGrowth2622K10P097 : ℚ := ((8357301908570228910988210237957088843 : ℚ) / 130362145366030563899357365553174937600)

theorem momentPanelPhase_owner2622K10P097 :
    (momentPanelPhase2622K10P097 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (3 / 40) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P097, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P097 :
    (momentPanelGrowth2622K10P097 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P097, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P097Input : RatPair2542 := (momentPanelPhase2622K10P097 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P097Expected : RatState2542 :=
  ((((189456729552309495456166851011468928625875929258091291254214417029757435840772667257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7505369389784158540535355449671143 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K10P097_replay :
    compactExp2620 momentScalarAmp2622K10P097Input 20 = momentScalarAmp2622K10P097Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P097_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (3 / 40) 0) -
      (momentScalarAmp2622K10P097Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P097]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P097 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P097 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P097Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P097_replay] at h
  simpa only [momentPanelPhase_owner2622K10P097] using h

theorem momentScalarAmp2622K10P097_radius_le :
    (momentScalarAmp2622K10P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P097Expected]

def momentScalarGrow2622K10P097Input : RatPair2542 := (momentPanelGrowth2622K10P097 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P097Expected : RatState2542 :=
  ((((2277406284123124100157641087452310711928036717143852357779831896657363935236872587912162560985321 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((721738816632035163037116898259432867528006344453 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K10P097_replay :
    compactExp2620 momentScalarGrow2622K10P097Input 20 = momentScalarGrow2622K10P097Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P097_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P097Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P097]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P097 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P097 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P097Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P097_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P097] using h

theorem momentScalarGrow2622K10P097_radius_le :
    (momentScalarGrow2622K10P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P097Expected]

end ConnesWeilRH.Dev
