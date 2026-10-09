import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P112 : ℚ := ((-2660542168352659002710991909798280641853149543830391 : ℚ) / 86719569808814122373101455503751324486615684874240)

def momentPanelGrowth2622K02P112 : ℚ := ((831006945822632965313515519509710760783059770549083013 : ℚ) / 4267463036778048702776905439738352375460189577202892800)

theorem momentPanelPhase_owner2622K02P112 :
    (momentPanelPhase2622K02P112 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P112, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P112 :
    (momentPanelGrowth2622K02P112 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P112, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P112Input : RatPair2542 := (momentPanelPhase2622K02P112 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P112Expected : RatState2542 :=
  ((((101278016897041248535119177339350760585206722636387717022855337069489793948829988333 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((128388895332596717642149370756983401 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P112_replay :
    compactExp2620 momentScalarAmp2622K02P112Input 20 = momentScalarAmp2622K02P112Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P112_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 40) 0) -
      (momentScalarAmp2622K02P112Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P112]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P112 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P112 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P112Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P112_replay] at h
  simpa only [momentPanelPhase_owner2622K02P112] using h

theorem momentScalarAmp2622K02P112_radius_le :
    (momentScalarAmp2622K02P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P112Expected]

def momentScalarGrow2622K02P112Input : RatPair2542 := (momentPanelGrowth2622K02P112 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P112Expected : RatState2542 :=
  ((((2595190069137610004896976732755425826565498021709178537040564722573638789464257633956155774465875 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3289793637901445113309136783911572135012039515119 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P112_replay :
    compactExp2620 momentScalarGrow2622K02P112Input 20 = momentScalarGrow2622K02P112Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P112_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P112Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P112Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P112 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P112]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P112 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P112 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P112Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P112Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P112_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P112] using h

theorem momentScalarGrow2622K02P112_radius_le :
    (momentScalarGrow2622K02P112Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P112Expected]

end ConnesWeilRH.Dev
