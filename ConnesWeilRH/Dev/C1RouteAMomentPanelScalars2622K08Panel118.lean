import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P118 : ℚ := ((-2400986651527056723092897690038632461217 : ℚ) / 74539883534380253975048543201237401600)

def momentPanelGrowth2622K08P118 : ℚ := ((6321096181213040607871391601849753990563 : ℚ) / 28357269896310438382884203296793926041600)

theorem momentPanelPhase_owner2622K08P118 :
    (momentPanelPhase2622K08P118 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (57 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P118 :
    (momentPanelGrowth2622K08P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P118Input : RatPair2542 := (momentPanelPhase2622K08P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P118Expected : RatState2542 :=
  ((((10954971112400722646660417103660320875382116663334894119352902987345244966310583391 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((27775004610222924571164655343872607 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K08P118_replay :
    compactExp2620 momentScalarAmp2622K08P118Input 20 = momentScalarAmp2622K08P118Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622K08P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P118]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P118 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P118_replay] at h
  simpa only [momentPanelPhase_owner2622K08P118] using h

theorem momentScalarAmp2622K08P118_radius_le :
    (momentScalarAmp2622K08P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P118Expected]

def momentScalarGrow2622K08P118Input : RatPair2542 := (momentPanelGrowth2622K08P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P118Expected : RatState2542 :=
  ((((2669358138418177750789800095618109651839256481805586561189450193658801540620980361284644064454231 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((105744147720298176062339651074211182111992582745 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K08P118_replay :
    compactExp2620 momentScalarGrow2622K08P118Input 20 = momentScalarGrow2622K08P118Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P118_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P118] using h

theorem momentScalarGrow2622K08P118_radius_le :
    (momentScalarGrow2622K08P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P118Expected]

end ConnesWeilRH.Dev
