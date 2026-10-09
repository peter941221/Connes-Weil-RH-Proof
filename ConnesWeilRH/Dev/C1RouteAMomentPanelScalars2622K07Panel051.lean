import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P051 : ℚ := ((-35315842907847970343926096359431620675 : ℚ) / 921389303474688084019075731421134848)

def momentPanelGrowth2622K07P051 : ℚ := ((1184670753864530467853559195718902954075 : ℚ) / 2916344436355929504350993394886730842112)

theorem momentPanelPhase_owner2622K07P051 :
    (momentPanelPhase2622K07P051 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-77 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P051, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P051 :
    (momentPanelGrowth2622K07P051 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P051, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P051Input : RatPair2542 := (momentPanelPhase2622K07P051 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P051Expected : RatState2542 :=
  ((((12064428775149868819116999413628545470775043931803885328850543146310154786403715 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((30588080039930107441746342613379 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P051_replay :
    compactExp2620 momentScalarAmp2622K07P051Input 20 = momentScalarAmp2622K07P051Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P051_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-77 / 200) 0) -
      (momentScalarAmp2622K07P051Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P051]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P051 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P051 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P051Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P051_replay] at h
  simpa only [momentPanelPhase_owner2622K07P051] using h

theorem momentScalarAmp2622K07P051_radius_le :
    (momentScalarAmp2622K07P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P051Expected]

def momentScalarGrow2622K07P051Input : RatPair2542 := (momentPanelGrowth2622K07P051 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P051Expected : RatState2542 :=
  ((((3206392778212968108500738181404304328071104708746970263483894591642703532220879384301168957533317 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4064584155251379921094604512212633648395532065723 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P051_replay :
    compactExp2620 momentScalarGrow2622K07P051Input 20 = momentScalarGrow2622K07P051Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P051_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P051Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P051]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P051 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P051 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P051Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P051_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P051] using h

theorem momentScalarGrow2622K07P051_radius_le :
    (momentScalarGrow2622K07P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P051Expected]

end ConnesWeilRH.Dev
