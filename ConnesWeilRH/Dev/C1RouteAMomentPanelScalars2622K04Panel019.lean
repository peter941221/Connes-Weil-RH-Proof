import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P019 : ℚ := ((-380881258002648669566509373504478036495033736001644533 : ℚ) / 5742959265910241369402331083870878529776895865651200)

def momentPanelGrowth2622K04P019 : ℚ := ((2137485174430274972104163807934601207011771606906344629 : ℚ) / 1169947332233699739792777032249257666832533296041164800)

theorem momentPanelPhase_owner2622K04P019 :
    (momentPanelPhase2622K04P019 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P019 :
    (momentPanelGrowth2622K04P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P019Input : RatPair2542 := (momentPanelPhase2622K04P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P019Expected : RatState2542 :=
  ((((33617739720411664968109384270742249139483628629157545553995290614499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417894257472690264831333 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P019_replay :
    compactExp2620 momentScalarAmp2622K04P019Input 20 = momentScalarAmp2622K04P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K04P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P019_replay] at h
  simpa only [momentPanelPhase_owner2622K04P019] using h

theorem momentScalarAmp2622K04P019_radius_le :
    (momentScalarAmp2622K04P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P019Expected]

def momentScalarGrow2622K04P019Input : RatPair2542 := (momentPanelGrowth2622K04P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P019Expected : RatState2542 :=
  ((((13275516839448096062599220315497812689036570533476033608036470307242864614924518077357852138969413 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8414343784138320693829421377456612120892267926619 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P019_replay :
    compactExp2620 momentScalarGrow2622K04P019Input 20 = momentScalarGrow2622K04P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P019] using h

theorem momentScalarGrow2622K04P019_radius_le :
    (momentScalarGrow2622K04P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P019Expected]

end ConnesWeilRH.Dev
