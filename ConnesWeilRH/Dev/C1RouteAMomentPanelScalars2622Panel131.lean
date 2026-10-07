import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P131 : ℚ := ((-1776268922393279322766945936600462684774684358559814559 : ℚ) / 50408104910066173463168967183405049024820398365081600)

def momentPanelGrowth2622P131 : ℚ := ((3830873304005895929064878010701705096156302688941871551 : ℚ) / 9681263160833208804014181216076344144459300864419430400)

theorem momentPanelPhase_owner2622P131 :
    (momentPanelPhase2622P131 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (83 / 200) 0 := by
  norm_num [momentPanelPhase2622P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P131 :
    (momentPanelGrowth2622P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P131Input : RatPair2542 := (momentPanelPhase2622P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P131Expected : RatState2542 :=
  ((((1061773785215110517981255300234316732080835334390261928887614822865376270524593537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((84125213169319871985432487580113 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622P131_replay :
    compactExp2620 momentScalarAmp2622P131Input 20 = momentScalarAmp2622P131Expected := by
  decide +kernel

theorem momentScalarAmp2622P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P131]
  have h := compactExp_real_error2620 momentPanelPhase2622P131 20 hsmall
  change |Real.exp (momentPanelPhase2622P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P131_replay] at h
  simpa only [momentPanelPhase_owner2622P131] using h

theorem momentScalarAmp2622P131_radius_le :
    (momentScalarAmp2622P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P131Expected]

def momentScalarGrow2622P131Input : RatPair2542 := (momentPanelGrowth2622P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P131Expected : RatState2542 :=
  ((((1586422387072689064926977119711815305809459242143349550487689756312230497285238021664006003699467 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2011028532288873158438095768960336381183209458261 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P131_replay :
    compactExp2620 momentScalarGrow2622P131Input 20 = momentScalarGrow2622P131Expected := by
  decide +kernel

theorem momentScalarGrow2622P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P131_replay] at h
  simpa only [momentPanelGrowth_owner2622P131] using h

theorem momentScalarGrow2622P131_radius_le :
    (momentScalarGrow2622P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P131Expected]

end ConnesWeilRH.Dev
