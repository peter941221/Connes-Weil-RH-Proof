import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K12
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K12P131 : ℚ := ((-796907933605194867488626290087706054801 : ℚ) / 22385695479550348646910581244375859200)

def momentPanelGrowth2622K12P131 : ℚ := ((1663828004018876284307217089974264933489 : ℚ) / 4299344507444939369029315841464519884800)

theorem momentPanelPhase_owner2622K12P131 :
    (momentPanelPhase2622K12P131 : ℝ) = momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (83 / 200) 0 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K12P131 :
    (momentPanelGrowth2622K12P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K12P131Input : RatPair2542 := (momentPanelPhase2622K12P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K12P131Expected : RatState2542 :=
  ((((739874199329524900009898103842622347280249429391644529716255243329803980230982277 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29310431795231492447502941023435 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K12P131_replay :
    compactExp2620 momentScalarAmp2622K12P131Input 20 = momentScalarAmp2622K12P131Expected := by
  decide +kernel

theorem momentScalarAmp2622K12P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622K12P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K12P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K12P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P131]
  have h := compactExp_real_error2620 momentPanelPhase2622K12P131 20 hsmall
  change |Real.exp (momentPanelPhase2622K12P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K12P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K12P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K12P131_replay] at h
  simpa only [momentPanelPhase_owner2622K12P131] using h

theorem momentScalarAmp2622K12P131_radius_le :
    (momentScalarAmp2622K12P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarAmp2622K12P131Expected]

def momentScalarGrow2622K12P131Input : RatPair2542 := (momentPanelGrowth2622K12P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K12P131Expected : RatState2542 :=
  ((((3145348172037704910026851945027283497730109709055172179254417561797363167359081767872363359957303 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((996800256665548215734357176044088432658044331471 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K12P131_replay :
    compactExp2620 momentScalarGrow2622K12P131Input 20 = momentScalarGrow2622K12P131Expected := by
  decide +kernel

theorem momentScalarGrow2622K12P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K12P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K12P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K12P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622K12P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622K12P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K12P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K12P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K12P131_replay] at h
  simpa only [momentPanelGrowth_owner2622K12P131] using h

theorem momentScalarGrow2622K12P131_radius_le :
    (momentScalarGrow2622K12P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarGrow2622K12P131Expected]

end ConnesWeilRH.Dev
