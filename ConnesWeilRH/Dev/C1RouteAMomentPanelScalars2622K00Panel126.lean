import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P126 : ℚ := ((-1780269195601814463189856898907961845660764913334279669 : ℚ) / 52783045070728890705249955036569008931761288747417600)

def momentPanelGrowth2622K00P126 : ℚ := ((18270416743879523076810146916811571733063795277151035277 : ℚ) / 56704863683902027220851629542512945097820418469579980800)

theorem momentPanelPhase_owner2622K00P126 :
    (momentPanelPhase2622K00P126 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (73 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P126 :
    (momentPanelGrowth2622K00P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P126Input : RatPair2542 := (momentPanelPhase2622K00P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P126Expected : RatState2542 :=
  ((((2402495125661745147707339678039143296558941164422079997289390425345620622274660959 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3045622351918816348683883303805289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P126_replay :
    compactExp2620 momentScalarAmp2622K00P126Input 20 = momentScalarAmp2622K00P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K00P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P126_replay] at h
  simpa only [momentPanelPhase_owner2622K00P126] using h

theorem momentScalarAmp2622K00P126_radius_le :
    (momentScalarAmp2622K00P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P126Expected]

def momentScalarGrow2622K00P126Input : RatPair2542 := (momentPanelGrowth2622K00P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P126Expected : RatState2542 :=
  ((((2948011235989739030288402314420948100719992211369659427495875782168113764435689313804164676353095 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3737047064477994033218136626165351842937583035329 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P126_replay :
    compactExp2620 momentScalarGrow2622K00P126Input 20 = momentScalarGrow2622K00P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P126] using h

theorem momentScalarGrow2622K00P126_radius_le :
    (momentScalarGrow2622K00P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P126Expected]

end ConnesWeilRH.Dev
