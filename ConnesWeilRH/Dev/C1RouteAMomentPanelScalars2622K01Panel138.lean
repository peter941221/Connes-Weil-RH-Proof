import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P138 : ℚ := ((-28479236231014278785094781513083009917854438195529243 : ℚ) / 727682236126133645357567101523825095284743366246400)

def momentPanelGrowth2622K01P138 : ℚ := ((350954563336174444281140184277104755625779011915148891 : ℚ) / 686801116608456707047453272557943135007413030302515200)

theorem momentPanelPhase_owner2622K01P138 :
    (momentPanelPhase2622K01P138 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P138 :
    (momentPanelGrowth2622K01P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P138Input : RatPair2542 := (momentPanelPhase2622K01P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P138Expected : RatState2542 :=
  ((((5377660085848106910777965442930479977323354184219262314191177441859381825448441 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((27268996325797793931249477181753 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P138_replay :
    compactExp2620 momentScalarAmp2622K01P138Input 20 = momentScalarAmp2622K01P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K01P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P138_replay] at h
  simpa only [momentPanelPhase_owner2622K01P138] using h

theorem momentScalarAmp2622K01P138_radius_le :
    (momentScalarAmp2622K01P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P138Expected]

def momentScalarGrow2622K01P138Input : RatPair2542 := (momentPanelGrowth2622K01P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P138Expected : RatState2542 :=
  ((((3560595037907659784280095579211260399277060490248692082944375024109124888826979979337161565066139 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1128397059345452579458797959957820538082203095797 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P138_replay :
    compactExp2620 momentScalarGrow2622K01P138Input 20 = momentScalarGrow2622K01P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P138] using h

theorem momentScalarGrow2622K01P138_radius_le :
    (momentScalarGrow2622K01P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P138Expected]

end ConnesWeilRH.Dev
