import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P148 : ℚ := ((-85430329729529176803168209350409155163951408421308349 : ℚ) / 1877615702139325521526228107109283326668322321203200)

def momentPanelGrowth2622K01P148 : ℚ := ((421979261725489146415819161530644830253211671343951851 : ℚ) / 505452170277852032640425340707751383988348478763827200)

theorem momentPanelPhase_owner2622K01P148 :
    (momentPanelPhase2622K01P148 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (117 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P148 :
    (momentPanelGrowth2622K01P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P148Input : RatPair2542 := (momentPanelPhase2622K01P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P148Expected : RatState2542 :=
  ((((9277131679680896933969744119305990566066678598010499217328773558347458631895 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((47045105232445857318920021209 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P148_replay :
    compactExp2620 momentScalarAmp2622K01P148Input 20 = momentScalarAmp2622K01P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K01P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P148_replay] at h
  simpa only [momentPanelPhase_owner2622K01P148] using h

theorem momentScalarAmp2622K01P148_radius_le :
    (momentScalarAmp2622K01P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P148Expected]

def momentScalarGrow2622K01P148Input : RatPair2542 := (momentPanelGrowth2622K01P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P148Expected : RatState2542 :=
  ((((4922339040094653120875399515492697525235042621941241539919515922516812040029541066264900725911749 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1559950267674395561352355014733459928306648539269 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P148_replay :
    compactExp2620 momentScalarGrow2622K01P148Input 20 = momentScalarGrow2622K01P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P148] using h

theorem momentScalarGrow2622K01P148_radius_le :
    (momentScalarGrow2622K01P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P148Expected]

end ConnesWeilRH.Dev
