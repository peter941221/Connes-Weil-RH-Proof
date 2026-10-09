import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P107 : ℚ := ((-14415085580025108823101414373415565133077409565531451 : ℚ) / 472247716562548005444565661571448950726323202949120)

def momentPanelGrowth2622K00P107 : ℚ := ((1864695602258731310794837999208632448905221307332841231 : ℚ) / 13362603097565086892104487849084571535595137948608102400)

theorem momentPanelPhase_owner2622K00P107 :
    (momentPanelPhase2622K00P107 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P107 :
    (momentPanelGrowth2622K00P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P107Input : RatPair2542 := (momentPanelPhase2622K00P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P107Expected : RatState2542 :=
  ((((118307789962930654557902996205523539956566682064286437855305961664446360720799892685 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((74988653394565162639322389480844727 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P107_replay :
    compactExp2620 momentScalarAmp2622K00P107Input 20 = momentScalarAmp2622K00P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K00P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P107_replay] at h
  simpa only [momentPanelPhase_owner2622K00P107] using h

theorem momentScalarAmp2622K00P107_radius_le :
    (momentScalarAmp2622K00P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P107Expected]

def momentScalarGrow2622K00P107Input : RatPair2542 := (momentPanelGrowth2622K00P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P107Expected : RatState2542 :=
  ((((2455854304854329305172332059891799547946319443813382874219201882968521720422298313797732668746393 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3113164769317696544407966551358340133837893812387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P107_replay :
    compactExp2620 momentScalarGrow2622K00P107Input 20 = momentScalarGrow2622K00P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P107] using h

theorem momentScalarGrow2622K00P107_radius_le :
    (momentScalarGrow2622K00P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P107Expected]

end ConnesWeilRH.Dev
