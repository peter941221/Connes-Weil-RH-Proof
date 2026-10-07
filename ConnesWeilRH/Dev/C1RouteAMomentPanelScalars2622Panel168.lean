import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P168 : ℚ := ((-1782495117547930992369803432443298901183786011428089201 : ℚ) / 23370324619444469476400797778153813161185646320025600)

def momentPanelGrowth2622P168 : ℚ := ((36341025991722356192831718873548495302841918581839314717 : ℚ) / 10755800269332438561122104783725275565970270293118156800)

theorem momentPanelPhase_owner2622P168 :
    (momentPanelPhase2622P168 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (157 / 200) 0 := by
  norm_num [momentPanelPhase2622P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P168 :
    (momentPanelGrowth2622P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P168Input : RatPair2542 := (momentPanelPhase2622P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P168Expected : RatState2542 :=
  ((((802004175311382969433212592454918807042131887115563375690802453 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851641262728536325829 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P168_replay :
    compactExp2620 momentScalarAmp2622P168Input 20 = momentScalarAmp2622P168Expected := by
  decide +kernel

theorem momentScalarAmp2622P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P168]
  have h := compactExp_real_error2620 momentPanelPhase2622P168 20 hsmall
  change |Real.exp (momentPanelPhase2622P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P168_replay] at h
  simpa only [momentPanelPhase_owner2622P168] using h

theorem momentScalarAmp2622P168_radius_le :
    (momentScalarAmp2622P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P168Expected]

def momentScalarGrow2622P168Input : RatPair2542 := (momentPanelGrowth2622P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P168Expected : RatState2542 :=
  ((((31328217129039615032768331639000030687948751963378237376011941369567725373566121789490015701984627 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((79426210566659407336814334977213669599799122946955 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P168_replay :
    compactExp2620 momentScalarGrow2622P168Input 20 = momentScalarGrow2622P168Expected := by
  decide +kernel

theorem momentScalarGrow2622P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P168_replay] at h
  simpa only [momentPanelGrowth_owner2622P168] using h

theorem momentScalarGrow2622P168_radius_le :
    (momentScalarGrow2622P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622P168Expected]

end ConnesWeilRH.Dev
