import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P029 : ℚ := ((-120148162447013020431551183789807932336120666447991027 : ℚ) / 2412904949288695774917138259951316477568671442534400)

def momentPanelGrowth2622K02P029 : ℚ := ((1817928441878330513014753122139698007657640397644401013 : ℚ) / 1875681353341401134099429812134888425909982784703692800)

theorem momentPanelPhase_owner2622K02P029 :
    (momentPanelPhase2622K02P029 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-121 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P029, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P029 :
    (momentPanelGrowth2622K02P029 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P029, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P029Input : RatPair2542 := (momentPanelPhase2622K02P029 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P029Expected : RatState2542 :=
  ((((126556360394902326872855941381834033212069110541051521724654791559181653935 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((10065082978217465873512643 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K02P029_replay :
    compactExp2620 momentScalarAmp2622K02P029Input 20 = momentScalarAmp2622K02P029Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P029_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-121 / 200) 0) -
      (momentScalarAmp2622K02P029Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P029]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P029 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P029 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P029Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P029_replay] at h
  simpa only [momentPanelPhase_owner2622K02P029] using h

theorem momentScalarAmp2622K02P029_radius_le :
    (momentScalarAmp2622K02P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P029Expected]

def momentScalarGrow2622K02P029Input : RatPair2542 := (momentPanelGrowth2622K02P029 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P029Expected : RatState2542 :=
  ((((5630163529580272935352413922185749916631258449559361032786955073726839412753347442069993835602839 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7137073580781583260367013617698691836853333566057 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P029_replay :
    compactExp2620 momentScalarGrow2622K02P029Input 20 = momentScalarGrow2622K02P029Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P029_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P029Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P029Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P029 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P029]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P029 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P029 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P029Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P029Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P029_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P029] using h

theorem momentScalarGrow2622K02P029_radius_le :
    (momentScalarGrow2622K02P029Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P029Expected]

end ConnesWeilRH.Dev
