import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P111 : ℚ := ((-1796667498273952092408647962873366843945743384176766599 : ℚ) / 58080988506053413783738312555165534878014044215705600)

def momentPanelGrowth2622K00P111 : ℚ := ((732210824602006736001806677383984454016868842803375637 : ℚ) / 4308111764690160793169385953291258721691938392427724800)

theorem momentPanelPhase_owner2622K00P111 :
    (momentPanelPhase2622K00P111 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (43 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P111 :
    (momentPanelGrowth2622K00P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P111Input : RatPair2542 := (momentPanelPhase2622K00P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P111Expected : RatState2542 :=
  ((((78560888950382573328835974719394685216762073018323411052381340326148049253022433309 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((99590695996740252114469455255011509 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P111_replay :
    compactExp2620 momentScalarAmp2622K00P111Input 20 = momentScalarAmp2622K00P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K00P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P111_replay] at h
  simpa only [momentPanelPhase_owner2622K00P111] using h

theorem momentScalarAmp2622K00P111_radius_le :
    (momentScalarAmp2622K00P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P111Expected]

def momentScalarGrow2622K00P111Input : RatPair2542 := (momentPanelGrowth2622K00P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P111Expected : RatState2542 :=
  ((((1265848482232364039786834883289242872805112724481031141888665900192634488397734847833408667432447 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1604653328205734055759121459170189675972938329883 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P111_replay :
    compactExp2620 momentScalarGrow2622K00P111Input 20 = momentScalarGrow2622K00P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P111] using h

theorem momentScalarGrow2622K00P111_radius_le :
    (momentScalarGrow2622K00P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P111Expected]

end ConnesWeilRH.Dev
