import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P011 : ℚ := ((-1871258975779326303139408649347408647956045346011910799 : ℚ) / 23370324619444469476400797778153813161185646320025600)

def momentPanelGrowth2622K00P011 : ℚ := ((36341025991722356192831718873548495302841918581839314717 : ℚ) / 10755800269332438561122104783725275565970270293118156800)

theorem momentPanelPhase_owner2622K00P011 :
    (momentPanelPhase2622K00P011 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-157 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P011 :
    (momentPanelGrowth2622K00P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P011Input : RatPair2542 := (momentPanelPhase2622K00P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P011Expected : RatState2542 :=
  ((((35949565380420451082347373183434044784263098481113292354150721 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639274833337381501 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P011_replay :
    compactExp2620 momentScalarAmp2622K00P011Input 20 = momentScalarAmp2622K00P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K00P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P011_replay] at h
  simpa only [momentPanelPhase_owner2622K00P011] using h

theorem momentScalarAmp2622K00P011_radius_le :
    (momentScalarAmp2622K00P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P011Expected]

def momentScalarGrow2622K00P011Input : RatPair2542 := (momentPanelGrowth2622K00P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P011Expected : RatState2542 :=
  ((((31328217129039615032768331639000030687948751963378237376011941369567725373566121789490015701984627 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((79426210566659407336814334977213669599799122946955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P011_replay :
    compactExp2620 momentScalarGrow2622K00P011Input 20 = momentScalarGrow2622K00P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P011] using h

theorem momentScalarGrow2622K00P011_radius_le :
    (momentScalarGrow2622K00P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622K00P011Expected]

end ConnesWeilRH.Dev
