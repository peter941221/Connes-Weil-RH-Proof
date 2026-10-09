import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P029 : ℚ := ((-73351657695126545795276877754415061152370454339439525 : ℚ) / 1544259167544765295946968486368842545643949723222016)

def momentPanelGrowth2622K03P029 : ℚ := ((1117948673360124585250823907937992143764402232115463475 : ℚ) / 1200436066138496725823635079766328592582388982210363392)

theorem momentPanelPhase_owner2622K03P029 :
    (momentPanelPhase2622K03P029 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-121 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P029, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P029 :
    (momentPanelGrowth2622K03P029 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P029, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P029Input : RatPair2542 := (momentPanelPhase2622K03P029 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P029Expected : RatState2542 :=
  ((((5021047151173840971499462748075776013529797586846063049770032062236887774627 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6367639619057211720302639363 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P029_replay :
    compactExp2620 momentScalarAmp2622K03P029Input 20 = momentScalarAmp2622K03P029Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P029_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-121 / 200) 0) -
      (momentScalarAmp2622K03P029Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P029]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P029 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P029 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P029Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P029_replay] at h
  simpa only [momentPanelPhase_owner2622K03P029] using h

theorem momentScalarAmp2622K03P029_radius_le :
    (momentScalarAmp2622K03P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P029Expected]

def momentScalarGrow2622K03P029Input : RatPair2542 := (momentPanelGrowth2622K03P029 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P029Expected : RatState2542 :=
  ((((1355160593797439869436300939172192526940597162515659974695386003594197604823866426088080384691235 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6871474457676951081421934123959698324580923346971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P029_replay :
    compactExp2620 momentScalarGrow2622K03P029Input 20 = momentScalarGrow2622K03P029Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P029_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P029Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P029]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P029 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P029 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P029Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P029_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P029] using h

theorem momentScalarGrow2622K03P029_radius_le :
    (momentScalarGrow2622K03P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P029Expected]

end ConnesWeilRH.Dev
