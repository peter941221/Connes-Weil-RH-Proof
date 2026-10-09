import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P128 : ℚ := ((-29587867823837375012705107755819579325 : ℚ) / 921389303474688084019075731421134848)

def momentPanelGrowth2622K07P128 : ℚ := ((1184670753864530467853559195718902954075 : ℚ) / 2916344436355929504350993394886730842112)

theorem momentPanelPhase_owner2622K07P128 :
    (momentPanelPhase2622K07P128 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P128 :
    (momentPanelGrowth2622K07P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P128Input : RatPair2542 := (momentPanelPhase2622K07P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P128Expected : RatState2542 :=
  ((((24178708563565138672673271772201214697111098921077805132296450069430035406108496055 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15325546544607333411385959930720279 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P128_replay :
    compactExp2620 momentScalarAmp2622K07P128Input 20 = momentScalarAmp2622K07P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K07P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P128_replay] at h
  simpa only [momentPanelPhase_owner2622K07P128] using h

theorem momentScalarAmp2622K07P128_radius_le :
    (momentScalarAmp2622K07P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P128Expected]

def momentScalarGrow2622K07P128Input : RatPair2542 := (momentPanelGrowth2622K07P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P128Expected : RatState2542 :=
  ((((3206392778212968108500738181404304328071104708746970263483894591642703532220879384301168957533317 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4064584155251379921094604512212633648395532065723 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P128_replay :
    compactExp2620 momentScalarGrow2622K07P128Input 20 = momentScalarGrow2622K07P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P128] using h

theorem momentScalarGrow2622K07P128_radius_le :
    (momentScalarGrow2622K07P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P128Expected]

end ConnesWeilRH.Dev
