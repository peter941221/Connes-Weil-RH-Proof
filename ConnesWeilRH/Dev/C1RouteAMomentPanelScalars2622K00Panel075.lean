import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P075 : ℚ := ((-1847789233095603049774595640936699028876424102455142927 : ℚ) / 59615565225250861847852181629517632048652773385830400)

def momentPanelGrowth2622K00P075 : ℚ := ((41329661282619819222558337938336768652448805300442951 : ℚ) / 349118487213727764121714907672653225512529098597990400)

theorem momentPanelPhase_owner2622K00P075 :
    (momentPanelPhase2622K00P075 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P075 :
    (momentPanelGrowth2622K00P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P075Input : RatPair2542 := (momentPanelPhase2622K00P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P075Expected : RatState2542 :=
  ((((73893503615741024686714544371117273844499773638487913038803230765172899471165855833 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((93673913100015986340412955919798687 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P075_replay :
    compactExp2620 momentScalarAmp2622K00P075Input 20 = momentScalarAmp2622K00P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K00P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P075_replay] at h
  simpa only [momentPanelPhase_owner2622K00P075] using h

theorem momentScalarAmp2622K00P075_radius_le :
    (momentScalarAmp2622K00P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P075Expected]

def momentScalarGrow2622K00P075Input : RatPair2542 := (momentPanelGrowth2622K00P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P075Expected : RatState2542 :=
  ((((300553416138076623379957769755621887972817536503251777754702536863212220288301340713074589653145 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1523986701416126206035314251347170123091132996855 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P075_replay :
    compactExp2620 momentScalarGrow2622K00P075Input 20 = momentScalarGrow2622K00P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P075] using h

theorem momentScalarGrow2622K00P075_radius_le :
    (momentScalarGrow2622K00P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P075Expected]

end ConnesWeilRH.Dev
