import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P097 : ℚ := ((-2712464026871969349829587536632103016074153122418133 : ℚ) / 90830043163807286830549319095765870479397995151360)

def momentPanelGrowth2622K02P097 : ℚ := ((1642130858411194266081086186806964437648448716502413 : ℚ) / 18346840915427302483039948651482425129659293027532800)

theorem momentPanelPhase_owner2622K02P097 :
    (momentPanelPhase2622K02P097 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P097, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P097 :
    (momentPanelGrowth2622K02P097 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P097, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P097Input : RatPair2542 := (momentPanelPhase2622K02P097 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P097Expected : RatState2542 :=
  ((((229209001666394579169243728580734730658562091495241345923758804481517072601359674113 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((290565203618202739457287278572147791 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P097_replay :
    compactExp2620 momentScalarAmp2622K02P097Input 20 = momentScalarAmp2622K02P097Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P097_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 40) 0) -
      (momentScalarAmp2622K02P097Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P097]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P097 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P097 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P097Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P097_replay] at h
  simpa only [momentPanelPhase_owner2622K02P097] using h

theorem momentScalarAmp2622K02P097_radius_le :
    (momentScalarAmp2622K02P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P097Expected]

def momentScalarGrow2622K02P097Input : RatPair2542 := (momentPanelGrowth2622K02P097 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P097Expected : RatState2542 :=
  ((((2335985086475929515250499690086601866193940216598768595726956067529210082288155738708071978698619 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2961212644230852734790986294691060647795358601219 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P097_replay :
    compactExp2620 momentScalarGrow2622K02P097Input 20 = momentScalarGrow2622K02P097Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P097_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P097Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P097Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P097 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P097]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P097 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P097 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P097Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P097Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P097_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P097] using h

theorem momentScalarGrow2622K02P097_radius_le :
    (momentScalarGrow2622K02P097Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P097Expected]

end ConnesWeilRH.Dev
