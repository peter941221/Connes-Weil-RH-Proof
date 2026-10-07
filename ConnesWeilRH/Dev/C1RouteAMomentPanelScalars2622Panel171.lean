import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P171 : ℚ := ((-1786562126428830591425926332914966809291940662462291279 : ℚ) / 20447321344782663639993428112721247121873781234073600)

def momentPanelGrowth2622P171 : ℚ := ((2353038226614721400650785693797832359050056251791961477 : ℚ) / 510582447790475923081886376082086830493454671072460800)

theorem momentPanelPhase_owner2622P171 :
    (momentPanelPhase2622P171 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (163 / 200) 0 := by
  norm_num [momentPanelPhase2622P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P171 :
    (momentPanelGrowth2622P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P171Input : RatPair2542 := (momentPanelPhase2622P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P171Expected : RatState2542 :=
  ((((24187877732689991569726460358037513075605466186664008959137 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229289014259703 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P171_replay :
    compactExp2620 momentScalarAmp2622P171Input 20 = momentScalarAmp2622P171Expected := by
  decide +kernel

theorem momentScalarAmp2622P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P171]
  have h := compactExp_real_error2620 momentPanelPhase2622P171 20 hsmall
  change |Real.exp (momentPanelPhase2622P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P171_replay] at h
  simpa only [momentPanelPhase_owner2622P171] using h

theorem momentScalarAmp2622P171_radius_le :
    (momentScalarAmp2622P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P171Expected]

def momentScalarGrow2622P171Input : RatPair2542 := (momentPanelGrowth2622P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P171Expected : RatState2542 :=
  ((((214319114903876705967322599358549580507943553547418261391380973537351569536789772749850380338891695 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((135840280298873815889683203580618076457771775977049 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P171_replay :
    compactExp2620 momentScalarGrow2622P171Input 20 = momentScalarGrow2622P171Expected := by
  decide +kernel

theorem momentScalarGrow2622P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P171_replay] at h
  simpa only [momentPanelGrowth_owner2622P171] using h

theorem momentScalarGrow2622P171_radius_le :
    (momentScalarGrow2622P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622P171Expected]

end ConnesWeilRH.Dev
