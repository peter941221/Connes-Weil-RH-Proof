import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P127 : ℚ := ((-68329001449476771451265316161136006857023523179305 : ℚ) / 2009564751329991512530066644984889152026907246592)

def momentPanelGrowth2622K00P127 : ℚ := ((1168962419529991771791349801798922238763270484238897397 : ℚ) / 3482728715007533370113854944014737886341250488782028800)

theorem momentPanelPhase_owner2622K00P127 :
    (momentPanelPhase2622K00P127 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (3 / 8) 0 := by
  norm_num [momentPanelPhase2622K00P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P127 :
    (momentPanelGrowth2622K00P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P127Input : RatPair2542 := (momentPanelPhase2622K00P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P127Expected : RatState2542 :=
  ((((456746291030614765918870942083929447023190181092273469960425320993876148828224675 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4632107883910299812709790703371455 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P127_replay :
    compactExp2620 momentScalarAmp2622K00P127Input 20 = momentScalarAmp2622K00P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K00P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P127_replay] at h
  simpa only [momentPanelPhase_owner2622K00P127] using h

theorem momentScalarAmp2622K00P127_radius_le :
    (momentScalarAmp2622K00P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P127Expected]

def momentScalarGrow2622K00P127Input : RatPair2542 := (momentPanelGrowth2622K00P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P127Expected : RatState2542 :=
  ((((2987910784171747135886976118386392801217663584582357722034242499595348631697158255042283958783089 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((59181651352775260780792926405366580435719711715 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarGrow2622K00P127_replay :
    compactExp2620 momentScalarGrow2622K00P127Input 20 = momentScalarGrow2622K00P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P127] using h

theorem momentScalarGrow2622K00P127_radius_le :
    (momentScalarGrow2622K00P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P127Expected]

end ConnesWeilRH.Dev
