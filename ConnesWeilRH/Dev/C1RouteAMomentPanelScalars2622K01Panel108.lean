import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P108 : ℚ := ((-28513297994339622797231085005885550050309325776045423 : ℚ) / 918933426948732269419377421430057443560031413862400)

def momentPanelGrowth2622K01P108 : ℚ := ((137646222951556845017922213242453720892267848176651211 : ℚ) / 1105050343965167426352059742761239886743831397479219200)

theorem momentPanelPhase_owner2622K01P108 :
    (momentPanelPhase2622K01P108 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (37 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P108 :
    (momentPanelGrowth2622K01P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P108Input : RatPair2542 := (momentPanelPhase2622K01P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P108Expected : RatState2542 :=
  ((((35725714461685277358144285729958451732080441192113386475653876003868445840301016315 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((90578127045742698461428997648727915 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P108_replay :
    compactExp2620 momentScalarAmp2622K01P108Input 20 = momentScalarAmp2622K01P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K01P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P108_replay] at h
  simpa only [momentPanelPhase_owner2622K01P108] using h

theorem momentScalarAmp2622K01P108_radius_le :
    (momentScalarAmp2622K01P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P108Expected]

def momentScalarGrow2622K01P108Input : RatPair2542 := (momentPanelGrowth2622K01P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P108Expected : RatState2542 :=
  ((((2419328190355914101314384930579129110404563070656567275732592506532319113453007555466211402233557 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((95839452135596573044291228678553704391330136825 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K01P108_replay :
    compactExp2620 momentScalarGrow2622K01P108Input 20 = momentScalarGrow2622K01P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P108] using h

theorem momentScalarGrow2622K01P108_radius_le :
    (momentScalarGrow2622K01P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P108Expected]

end ConnesWeilRH.Dev
