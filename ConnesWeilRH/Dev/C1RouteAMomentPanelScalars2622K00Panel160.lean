import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P160 : ℚ := ((-5323913959598190084766857250655883694663279558013993091 : ℚ) / 91887348254563861910437297341934056476430333850419200)

def momentPanelGrowth2622K00P160 : ℚ := ((32879921432061771203395909743818429568947773049692985917 : ℚ) / 18719157315739195836684432515988122669320532736658636800)

theorem momentPanelPhase_owner2622K00P160 :
    (momentPanelPhase2622K00P160 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (141 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P160 :
    (momentPanelGrowth2622K00P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P160Input : RatPair2542 := (momentPanelPhase2622K00P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P160Expected : RatState2542 :=
  ((((146811694605172913937303921769584705344079060443888974832136382598174023 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1301983927837506128441975 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P160_replay :
    compactExp2620 momentScalarAmp2622K00P160Input 20 = momentScalarAmp2622K00P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K00P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P160_replay] at h
  simpa only [momentPanelPhase_owner2622K00P160] using h

theorem momentScalarAmp2622K00P160_radius_le :
    (momentScalarAmp2622K00P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622K00P160Expected]

def momentScalarGrow2622K00P160Input : RatPair2542 := (momentPanelGrowth2622K00P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P160Expected : RatState2542 :=
  ((((12371729363468933164976358714846060022784875513833854450281455239621099717302519259048590757028369 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15683003882609415472089096887057828703511201691683 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P160_replay :
    compactExp2620 momentScalarGrow2622K00P160Input 20 = momentScalarGrow2622K00P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P160] using h

theorem momentScalarGrow2622K00P160_radius_le :
    (momentScalarGrow2622K00P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P160Expected]

end ConnesWeilRH.Dev
