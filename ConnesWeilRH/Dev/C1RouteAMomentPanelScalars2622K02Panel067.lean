import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P067 : ℚ := ((-2820088971638226940552826212887780681856597492329609 : ℚ) / 86719569808814122373101455503751324486615684874240)

def momentPanelGrowth2622K02P067 : ℚ := ((831006945822632965313515519509710760783059770549083013 : ℚ) / 4267463036778048702776905439738352375460189577202892800)

theorem momentPanelPhase_owner2622K02P067 :
    (momentPanelPhase2622K02P067 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-9 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P067, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P067 :
    (momentPanelGrowth2622K02P067 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-9 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P067, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P067Input : RatPair2542 := (momentPanelPhase2622K02P067 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P067Expected : RatState2542 :=
  ((((16087905488640622654032005940772057981681087457009206211126560565552935475433303239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((20394475538487289707190308558410345 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P067_replay :
    compactExp2620 momentScalarAmp2622K02P067Input 20 = momentScalarAmp2622K02P067Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P067_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-9 / 40) 0) -
      (momentScalarAmp2622K02P067Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P067]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P067 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P067 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P067Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P067_replay] at h
  simpa only [momentPanelPhase_owner2622K02P067] using h

theorem momentScalarAmp2622K02P067_radius_le :
    (momentScalarAmp2622K02P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P067Expected]

def momentScalarGrow2622K02P067Input : RatPair2542 := (momentPanelGrowth2622K02P067 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P067Expected : RatState2542 :=
  ((((2595190069137610004896976732755425826565498021709178537040564722573638789464257633956155774465875 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3289793637901445113309136783911572135012039515119 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P067_replay :
    compactExp2620 momentScalarGrow2622K02P067Input 20 = momentScalarGrow2622K02P067Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P067_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-9 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P067Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P067Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P067]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P067 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P067 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P067Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P067Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P067_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P067] using h

theorem momentScalarGrow2622K02P067_radius_le :
    (momentScalarGrow2622K02P067Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P067Expected]

end ConnesWeilRH.Dev
