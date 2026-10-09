import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P160 : ℚ := ((-325986194070451872107085667541555636404562683729144059 : ℚ) / 5742959265910241369402331083870878529776895865651200)

def momentPanelGrowth2622K02P160 : ℚ := ((2074524411948225089855286224332840666058253465407496133 : ℚ) / 1169947332233699739792777032249257666832533296041164800)

theorem momentPanelPhase_owner2622K02P160 :
    (momentPanelPhase2622K02P160 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P160 :
    (momentPanelGrowth2622K02P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P160Input : RatPair2542 := (momentPanelPhase2622K02P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P160Expected : RatState2542 :=
  ((((476263187587711460774460967824566484134117196114602674692918640588733379 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3021619637842214395101369 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P160_replay :
    compactExp2620 momentScalarAmp2622K02P160Input 20 = momentScalarAmp2622K02P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K02P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P160_replay] at h
  simpa only [momentPanelPhase_owner2622K02P160] using h

theorem momentScalarAmp2622K02P160_radius_le :
    (momentScalarAmp2622K02P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P160Expected]

def momentScalarGrow2622K02P160Input : RatPair2542 := (momentPanelGrowth2622K02P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P160Expected : RatState2542 :=
  ((((12579977461561178735310416902861563782814280497796464289265632732783429125693227911595372681084579 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((996686813317694626371376011240990822574754452301 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K02P160_replay :
    compactExp2620 momentScalarGrow2622K02P160Input 20 = momentScalarGrow2622K02P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P160] using h

theorem momentScalarGrow2622K02P160_radius_le :
    (momentScalarGrow2622K02P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P160Expected]

end ConnesWeilRH.Dev
