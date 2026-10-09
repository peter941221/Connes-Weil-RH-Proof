import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P081 : ℚ := ((-1839308720187222821407792492174102962182591015832872659 : ℚ) / 60455928666716131025819300408329494784954934598041600)

def momentPanelGrowth2622K00P081 : ℚ := ((17766762200709479753538110740626802596040323363216826231 : ℚ) / 224675187488838683042070075341899023447879072111552102400)

theorem momentPanelPhase_owner2622K00P081 :
    (momentPanelPhase2622K00P081 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P081 :
    (momentPanelGrowth2622K00P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P081Input : RatPair2542 := (momentPanelPhase2622K00P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P081Expected : RatState2542 :=
  ((((65404996231829372525666420830087281596438026739022008507254569793191367122717297049 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((165826176766706949022857631226680139 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P081_replay :
    compactExp2620 momentScalarAmp2622K00P081Input 20 = momentScalarAmp2622K00P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K00P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P081_replay] at h
  simpa only [momentPanelPhase_owner2622K00P081] using h

theorem momentScalarAmp2622K00P081_radius_le :
    (momentScalarAmp2622K00P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P081Expected]

def momentScalarGrow2622K00P081Input : RatPair2542 := (momentPanelGrowth2622K00P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P081Expected : RatState2542 :=
  ((((2311753659649769016907138838867016532036597973326115606871401471038439098954520247637461890240631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2930495693233770284630822534797870139683042336865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P081_replay :
    compactExp2620 momentScalarGrow2622K00P081Input 20 = momentScalarGrow2622K00P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P081] using h

theorem momentScalarGrow2622K00P081_radius_le :
    (momentScalarGrow2622K00P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P081Expected]

end ConnesWeilRH.Dev
