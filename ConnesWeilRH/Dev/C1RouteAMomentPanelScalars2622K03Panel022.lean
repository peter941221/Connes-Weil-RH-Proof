import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P022 : ℚ := ((-8800805634953545510614951693844256503768918133309625 : ℚ) / 159120990764402055219426186161985313765039655616512)

def momentPanelGrowth2622K03P022 : ℚ := ((18995383252593057277608569925290624078293146198475 : ℚ) / 13427546292977670560996354400580850243088880238592)

theorem momentPanelPhase_owner2622K03P022 :
    (momentPanelPhase2622K03P022 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P022, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P022 :
    (momentPanelGrowth2622K03P022 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P022, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P022Input : RatPair2542 := (momentPanelPhase2622K03P022 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P022Expected : RatState2542 :=
  ((((2038225240726920650801217604281418956904777040659143642538057916061355933 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1250436344309050310096729 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P022_replay :
    compactExp2620 momentScalarAmp2622K03P022Input 20 = momentScalarAmp2622K03P022Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P022_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 40) 0) -
      (momentScalarAmp2622K03P022Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P022]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P022 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P022 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P022Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P022_replay] at h
  simpa only [momentPanelPhase_owner2622K03P022] using h

theorem momentScalarAmp2622K03P022_radius_le :
    (momentScalarAmp2622K03P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P022Expected]

def momentScalarGrow2622K03P022Input : RatPair2542 := (momentPanelGrowth2622K03P022 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P022Expected : RatState2542 :=
  ((((8789753457613957263423302228278082494057680247673537987446376070447605734349119466352343473567473 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11142321214032515202606459218131970488558345061443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P022_replay :
    compactExp2620 momentScalarGrow2622K03P022Input 20 = momentScalarGrow2622K03P022Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P022_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P022Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P022Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P022 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P022]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P022 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P022 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P022Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P022Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P022_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P022] using h

theorem momentScalarGrow2622K03P022_radius_le :
    (momentScalarGrow2622K03P022Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P022Expected]

end ConnesWeilRH.Dev
