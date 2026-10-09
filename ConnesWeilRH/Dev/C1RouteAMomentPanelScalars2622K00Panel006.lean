import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P006 : ℚ := ((-1864121904990614042522976288892971186350289968697822309 : ℚ) / 18437756593452672127463361467736357969846873987481600)

def momentPanelGrowth2622K00P006 : ℚ := ((7053959216577542495684012256583958444315285445133159 : ℚ) / 1208022447106324443327733244542052683434356742553600)

theorem momentPanelPhase_owner2622K00P006 :
    (momentPanelPhase2622K00P006 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-167 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P006, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P006 :
    (momentPanelGrowth2622K00P006 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P006, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P006Input : RatPair2542 := (momentPanelPhase2622K00P006 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P006Expected : RatState2542 :=
  ((((26357377225610918392796788396776805696604863727821579 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349446305 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P006_replay :
    compactExp2620 momentScalarAmp2622K00P006Input 20 = momentScalarAmp2622K00P006Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P006_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-167 / 200) 0) -
      (momentScalarAmp2622K00P006Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P006]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P006 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P006 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P006Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P006_replay] at h
  simpa only [momentPanelPhase_owner2622K00P006] using h

theorem momentScalarAmp2622K00P006_radius_le :
    (momentScalarAmp2622K00P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P006Expected]

def momentScalarGrow2622K00P006Input : RatPair2542 := (momentPanelGrowth2622K00P006 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P006Expected : RatState2542 :=
  ((((733766280336612522098001877967198402548742815089110478297209499426757904829490643622435760751304115 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((465077042941155328747898304488575229884251319670969 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P006_replay :
    compactExp2620 momentScalarGrow2622K00P006Input 20 = momentScalarGrow2622K00P006Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P006_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P006Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P006]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P006 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P006 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P006Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P006_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P006] using h

theorem momentScalarGrow2622K00P006_radius_le :
    (momentScalarGrow2622K00P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622K00P006Expected]

end ConnesWeilRH.Dev
