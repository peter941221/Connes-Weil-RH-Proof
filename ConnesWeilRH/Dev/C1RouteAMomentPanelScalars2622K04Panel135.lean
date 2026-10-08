import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P135 : ℚ := ((-101175522242536658736340204851900511591881101551496639 : ℚ) / 3018057970996022764485851510997902415394956011110400)

def momentPanelGrowth2622K04P135 : ℚ := ((99569203433271039089778016580264929878690763463003069 : ℚ) / 184821011792650463009678424128071537837342859250892800)

theorem momentPanelPhase_owner2622K04P135 :
    (momentPanelPhase2622K04P135 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (91 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P135, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P135 :
    (momentPanelGrowth2622K04P135 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P135, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P135Input : RatPair2542 := (momentPanelPhase2622K04P135 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P135Expected : RatState2542 :=
  ((((5896266042046417722972871084738707935545576676924384046807162540781610176455996575 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7474644153208469267596862474926091 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P135_replay :
    compactExp2620 momentScalarAmp2622K04P135Input 20 = momentScalarAmp2622K04P135Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P135_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (91 / 200) 0) -
      (momentScalarAmp2622K04P135Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P135]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P135 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P135 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P135Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P135_replay] at h
  simpa only [momentPanelPhase_owner2622K04P135] using h

theorem momentScalarAmp2622K04P135_radius_le :
    (momentScalarAmp2622K04P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P135Expected]

def momentScalarGrow2622K04P135Input : RatPair2542 := (momentPanelGrowth2622K04P135 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P135Expected : RatState2542 :=
  ((((915181957751765641329217336901089964430189352706807481597917185088699538540671150597599410079089 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4640521448059331572636758935097412078226577932133 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P135_replay :
    compactExp2620 momentScalarGrow2622K04P135Input 20 = momentScalarGrow2622K04P135Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P135_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P135Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P135]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P135 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P135 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P135Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P135_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P135] using h

theorem momentScalarGrow2622K04P135_radius_le :
    (momentScalarGrow2622K04P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P135Expected]

end ConnesWeilRH.Dev
