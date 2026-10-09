import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P021 : ℚ := ((-1880439550310390653857256235540755016635079548365461579 : ℚ) / 32322022148096249850398367378541046656578233145753600)

def momentPanelGrowth2622K00P021 : ℚ := ((96057196829084216466054741288898688150782532902442109991 : ℚ) / 62678144189874077242483812889732154235533998242031206400)

theorem momentPanelPhase_owner2622K00P021 :
    (momentPanelPhase2622K00P021 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-137 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P021, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P021 :
    (momentPanelGrowth2622K00P021 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P021, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P021Input : RatPair2542 := (momentPanelPhase2622K00P021 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P021Expected : RatState2542 :=
  ((((115636262004616530668628311639402507846422607542279640780136140878310583 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2564446149465075620568171 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P021_replay :
    compactExp2620 momentScalarAmp2622K00P021Input 20 = momentScalarAmp2622K00P021Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P021_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-137 / 200) 0) -
      (momentScalarAmp2622K00P021Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P021]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P021 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P021 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P021Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P021_replay] at h
  simpa only [momentPanelPhase_owner2622K00P021] using h

theorem momentScalarAmp2622K00P021_radius_le :
    (momentScalarAmp2622K00P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P021Expected]

def momentScalarGrow2622K00P021Input : RatPair2542 := (momentPanelGrowth2622K00P021 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P021Expected : RatState2542 :=
  ((((9657735931470978617976015774938198109567023141116342680738010055552323922867335079515309485951 : ℚ) / 2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024), 0), ((12536439661729168544957978140090974126015754605115 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P021_replay :
    compactExp2620 momentScalarGrow2622K00P021Input 20 = momentScalarGrow2622K00P021Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P021_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P021Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P021Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P021 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P021]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P021 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P021 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P021Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P021Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P021_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P021] using h

theorem momentScalarGrow2622K00P021_radius_le :
    (momentScalarGrow2622K00P021Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P021Expected]

end ConnesWeilRH.Dev
