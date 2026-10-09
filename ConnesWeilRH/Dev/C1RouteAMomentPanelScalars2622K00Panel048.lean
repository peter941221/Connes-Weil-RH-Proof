import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P048 : ℚ := ((-1877485170933977972742266145190244864365146998880185441 : ℚ) / 50408104910066173463168967183405049024820398365081600)

def momentPanelGrowth2622K00P048 : ℚ := ((3830873304005895929064878010701705096156302688941871551 : ℚ) / 9681263160833208804014181216076344144459300864419430400)

theorem momentPanelPhase_owner2622K00P048 :
    (momentPanelPhase2622K00P048 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-83 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P048 :
    (momentPanelGrowth2622K00P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P048Input : RatPair2542 := (momentPanelPhase2622K00P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P048Expected : RatState2542 :=
  ((((142559601847280477999534291728974932303445323144885666524048515948891407099936405 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((180722186454226777065062715697397 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P048_replay :
    compactExp2620 momentScalarAmp2622K00P048Input 20 = momentScalarAmp2622K00P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K00P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P048_replay] at h
  simpa only [momentPanelPhase_owner2622K00P048] using h

theorem momentScalarAmp2622K00P048_radius_le :
    (momentScalarAmp2622K00P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P048Expected]

def momentScalarGrow2622K00P048Input : RatPair2542 := (momentPanelGrowth2622K00P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P048Expected : RatState2542 :=
  ((((1586422387072689064926977119711815305809459242143349550487689756312230497285238021664006003699467 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2011028532288873158438095768960336381183209458261 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P048_replay :
    compactExp2620 momentScalarGrow2622K00P048Input 20 = momentScalarGrow2622K00P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P048] using h

theorem momentScalarGrow2622K00P048_radius_le :
    (momentScalarGrow2622K00P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P048Expected]

end ConnesWeilRH.Dev
