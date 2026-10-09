import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P100 : ℚ := ((-337691894796915945913984697801582725141616181008325219 : ℚ) / 11292098295151013386956946933090515620033014739763200)

def momentPanelGrowth2622K02P100 : ℚ := ((503823485511550212366752808574343386805976150289139413 : ℚ) / 4643057539590549105076203975458681515550673178774732800)

theorem momentPanelPhase_owner2622K02P100 :
    (momentPanelPhase2622K02P100 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P100 :
    (momentPanelGrowth2622K02P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P100Input : RatPair2542 := (momentPanelPhase2622K02P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P100Expected : RatState2542 :=
  ((((54941047994932666241361876876720917825347619932303104644204009406772331149226650595 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((278592155146089457894521945323575499 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P100_replay :
    compactExp2620 momentScalarAmp2622K02P100Input 20 = momentScalarAmp2622K02P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K02P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P100_replay] at h
  simpa only [momentPanelPhase_owner2622K02P100] using h

theorem momentScalarAmp2622K02P100_radius_le :
    (momentScalarAmp2622K02P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P100Expected]

def momentScalarGrow2622K02P100Input : RatPair2542 := (momentPanelGrowth2622K02P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P100Expected : RatState2542 :=
  ((((2380808166509429457426747154650060953458067490695942212125101521481713450650368377298472620441397 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3018032588984969415098866155805504912134999247031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P100_replay :
    compactExp2620 momentScalarGrow2622K02P100Input 20 = momentScalarGrow2622K02P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P100] using h

theorem momentScalarGrow2622K02P100_radius_le :
    (momentScalarGrow2622K02P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P100Expected]

end ConnesWeilRH.Dev
