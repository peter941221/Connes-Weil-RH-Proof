import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P069 : ℚ := ((-1855808341752668742955483137756300578352738271890887403 : ℚ) / 58336751292586321794423957400890884406453832410726400)

def momentPanelGrowth2622K00P069 : ℚ := ((33821274930720736016464691464476055258426742533802456551 : ℚ) / 208662427487127311581636177932847158078396304196003430400)

theorem momentPanelPhase_owner2622K00P069 :
    (momentPanelPhase2622K00P069 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-41 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P069, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P069 :
    (momentPanelGrowth2622K00P069 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P069, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P069Input : RatPair2542 := (momentPanelPhase2622K00P069 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P069Expected : RatState2542 :=
  ((((32645660533903612632419807322071202381508819335979165142902697382042367762813907465 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((41384546690027881207958320276390043 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P069_replay :
    compactExp2620 momentScalarAmp2622K00P069Input 20 = momentScalarAmp2622K00P069Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P069_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-41 / 200) 0) -
      (momentScalarAmp2622K00P069Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P069]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P069 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P069 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P069Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P069_replay] at h
  simpa only [momentPanelPhase_owner2622K00P069] using h

theorem momentScalarAmp2622K00P069_radius_le :
    (momentScalarAmp2622K00P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P069Expected]

def momentScalarGrow2622K00P069Input : RatPair2542 := (momentPanelGrowth2622K00P069 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P069Expected : RatState2542 :=
  ((((2511838441456894035028202280192601783410070852310594342871827817057577897146604944075137114692501 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1592066507897174453719122510239014892516773812039 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P069_replay :
    compactExp2620 momentScalarGrow2622K00P069Input 20 = momentScalarGrow2622K00P069Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P069_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P069Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P069]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P069 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P069 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P069Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P069_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P069] using h

theorem momentScalarGrow2622K00P069_radius_le :
    (momentScalarGrow2622K00P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P069Expected]

end ConnesWeilRH.Dev
