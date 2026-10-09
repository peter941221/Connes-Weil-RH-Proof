import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P071 : ℚ := ((-1853198358221885229985727503130482454379502672805611479 : ℚ) / 58811739324718865242840154971523676387842010487193600)

def momentPanelGrowth2622K00P071 : ℚ := ((10388602158609377523562423910883449902375578855007492397 : ℚ) / 70723222013770715286531823536719352751605209438670028800)

theorem momentPanelPhase_owner2622K00P071 :
    (momentPanelPhase2622K00P071 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-37 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P071, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P071 :
    (momentPanelGrowth2622K00P071 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P071, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P071Input : RatPair2542 := (momentPanelPhase2622K00P071 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P071Expected : RatState2542 :=
  ((((44124598810702846428744804096256975273810029310640714569338103471704116189424692513 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((55936255081069624174720874912140439 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P071_replay :
    compactExp2620 momentScalarAmp2622K00P071Input 20 = momentScalarAmp2622K00P071Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P071_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-37 / 200) 0) -
      (momentScalarAmp2622K00P071Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P071]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P071 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P071 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P071Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P071_replay] at h
  simpa only [momentPanelPhase_owner2622K00P071] using h

theorem momentScalarAmp2622K00P071_radius_le :
    (momentScalarAmp2622K00P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P071Expected]

def momentScalarGrow2622K00P071Input : RatPair2542 := (momentPanelGrowth2622K00P071 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P071Expected : RatState2542 :=
  ((((2473959279203869018101417280957202207253900232130738349192791148900635409464431580757879610381861 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3136115525896638242119643812678794184365289150089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P071_replay :
    compactExp2620 momentScalarGrow2622K00P071Input 20 = momentScalarGrow2622K00P071Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P071_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P071Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P071]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P071 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P071 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P071Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P071_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P071] using h

theorem momentScalarGrow2622K00P071_radius_le :
    (momentScalarGrow2622K00P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P071Expected]

end ConnesWeilRH.Dev
