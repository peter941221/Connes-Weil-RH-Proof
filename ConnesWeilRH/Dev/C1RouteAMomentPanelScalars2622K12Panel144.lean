import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K12
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K12P144 : ℚ := ((-795249526190476460665725353908948203567 : ℚ) / 19010702521502710688365758630382796800)

def momentPanelGrowth2622K12P144 : ℚ := ((18256062144143389676763564567284309443 : ℚ) / 26313384099297494624507966455912857600)

theorem momentPanelPhase_owner2622K12P144 :
    (momentPanelPhase2622K12P144 : ℝ) = momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (109 / 200) 0 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K12P144 :
    (momentPanelGrowth2622K12P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K12P144Input : RatPair2542 := (momentPanelPhase2622K12P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K12P144Expected : RatState2542 :=
  ((((1453225682879610966595195891150057987554086329911973470285620733288218440210337 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((921129160066182806922459082657 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K12P144_replay :
    compactExp2620 momentScalarAmp2622K12P144Input 20 = momentScalarAmp2622K12P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K12P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K12P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K12P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K12P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K12P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K12P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K12P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K12P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K12P144_replay] at h
  simpa only [momentPanelPhase_owner2622K12P144] using h

theorem momentScalarAmp2622K12P144_radius_le :
    (momentScalarAmp2622K12P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarAmp2622K12P144Expected]

def momentScalarGrow2622K12P144Input : RatPair2542 := (momentPanelGrowth2622K12P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K12P144Expected : RatState2542 :=
  ((((4274737208978319746441751177034573736271641883928357062196486434045199901271999809317491992502291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5418869603365138357168890170795796708692559936083 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K12P144_replay :
    compactExp2620 momentScalarGrow2622K12P144Input 20 = momentScalarGrow2622K12P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K12P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K12P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K12P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K12P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K12P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K12P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K12P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K12P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K12P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K12P144] using h

theorem momentScalarGrow2622K12P144_radius_le :
    (momentScalarGrow2622K12P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarGrow2622K12P144Expected]

end ConnesWeilRH.Dev
