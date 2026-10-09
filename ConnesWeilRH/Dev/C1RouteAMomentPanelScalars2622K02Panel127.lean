import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P127 : ℚ := ((-4191942388826014952080861681165691231445532165521 : ℚ) / 125597796958124469533129165311555572001681702912)

def momentPanelGrowth2622K02P127 : ℚ := ((76693612434417545413766001019479288216331971127886653 : ℚ) / 217670544687970835632115934000921117896328155548876800)

theorem momentPanelPhase_owner2622K02P127 :
    (momentPanelPhase2622K02P127 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P127 :
    (momentPanelGrowth2622K02P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P127Input : RatPair2542 := (momentPanelPhase2622K02P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P127Expected : RatState2542 :=
  ((((6833126560462331506445680103313343876316205176973319888434179649690700402204046217 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8662292702537120104323467821550423 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P127_replay :
    compactExp2620 momentScalarAmp2622K02P127Input 20 = momentScalarAmp2622K02P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K02P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P127_replay] at h
  simpa only [momentPanelPhase_owner2622K02P127] using h

theorem momentScalarAmp2622K02P127_radius_le :
    (momentScalarAmp2622K02P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P127Expected]

def momentScalarGrow2622K02P127Input : RatPair2542 := (momentPanelGrowth2622K02P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P127Expected : RatState2542 :=
  ((((3038205025162047057885920601630192803195109267920943112247090580234683640532048796248768970219987 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((481422641204775897678039146435471003545115299489 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P127_replay :
    compactExp2620 momentScalarGrow2622K02P127Input 20 = momentScalarGrow2622K02P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P127] using h

theorem momentScalarGrow2622K02P127_radius_le :
    (momentScalarGrow2622K02P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P127Expected]

end ConnesWeilRH.Dev
