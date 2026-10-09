import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P108 : ℚ := ((-1800555735105372065523484578660225094760328684634388521 : ℚ) / 58811739324718865242840154971523676387842010487193600)

def momentPanelGrowth2622K00P108 : ℚ := ((10388602158609377523562423910883449902375578855007492397 : ℚ) / 70723222013770715286531823536719352751605209438670028800)

theorem momentPanelPhase_owner2622K00P108 :
    (momentPanelPhase2622K00P108 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (37 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P108 :
    (momentPanelGrowth2622K00P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P108Input : RatPair2542 := (momentPanelPhase2622K00P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P108Expected : RatState2542 :=
  ((((107998941170942970511391049221972018043268010104200406019224518410660423219274344975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((68454459956838743706981770239043541 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P108_replay :
    compactExp2620 momentScalarAmp2622K00P108Input 20 = momentScalarAmp2622K00P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K00P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P108_replay] at h
  simpa only [momentPanelPhase_owner2622K00P108] using h

theorem momentScalarAmp2622K00P108_radius_le :
    (momentScalarAmp2622K00P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P108Expected]

def momentScalarGrow2622K00P108Input : RatPair2542 := (momentPanelGrowth2622K00P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P108Expected : RatState2542 :=
  ((((2473959279203869018101417280957202207253900232130738349192791148900635409464431580757879610381861 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3136115525896638242119643812678794184365289150089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P108_replay :
    compactExp2620 momentScalarGrow2622K00P108Input 20 = momentScalarGrow2622K00P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P108] using h

theorem momentScalarGrow2622K00P108_radius_le :
    (momentScalarGrow2622K00P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P108Expected]

end ConnesWeilRH.Dev
