import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P033 : ℚ := ((-73352438630637673521330562575697660638855011353210925 : ℚ) / 1658256295256575723566855903320712621177112461574144)

def momentPanelGrowth2622K03P033 : ℚ := ((3136283820998438212643224483830146186723578298215888425 : ℚ) / 4163087505280929295684628633722634226257612577162919936)

theorem momentPanelPhase_owner2622K03P033 :
    (momentPanelPhase2622K03P033 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-113 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P033, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P033 :
    (momentPanelGrowth2622K03P033 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P033, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P033Input : RatPair2542 := (momentPanelPhase2622K03P033 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P033Expected : RatState2542 :=
  ((((131437909262218708696255779315908304202857883095408885658038824461616098623283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((166626791401450375378957407749 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P033_replay :
    compactExp2620 momentScalarAmp2622K03P033Input 20 = momentScalarAmp2622K03P033Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P033_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-113 / 200) 0) -
      (momentScalarAmp2622K03P033Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P033]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P033 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P033 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P033Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P033_replay] at h
  simpa only [momentPanelPhase_owner2622K03P033] using h

theorem momentScalarAmp2622K03P033_radius_le :
    (momentScalarAmp2622K03P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P033Expected]

def momentScalarGrow2622K03P033Input : RatPair2542 := (momentPanelGrowth2622K03P033 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P033Expected : RatState2542 :=
  ((((4537082117336795805718647541221294790260876134878705842478337322695240163164363128967052072113919 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5751430737177929367906491133958239051628195047943 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P033_replay :
    compactExp2620 momentScalarGrow2622K03P033Input 20 = momentScalarGrow2622K03P033Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P033_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P033Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P033]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P033 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P033 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P033Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P033_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P033] using h

theorem momentScalarGrow2622K03P033_radius_le :
    (momentScalarGrow2622K03P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P033Expected]

end ConnesWeilRH.Dev
