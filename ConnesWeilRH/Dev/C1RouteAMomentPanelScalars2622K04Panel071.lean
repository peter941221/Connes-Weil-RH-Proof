import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P071 : ℚ := ((-120619484445332794042716710600711018769237108779010623 : ℚ) / 3675733707794929077677509685720229774240125655449600)

def momentPanelGrowth2622K04P071 : ℚ := ((960945071825609943448379264228110548896318239520292389 : ℚ) / 4420201375860669705408238971044959546975325589916876800)

theorem momentPanelPhase_owner2622K04P071 :
    (momentPanelPhase2622K04P071 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-37 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P071, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P071 :
    (momentPanelGrowth2622K04P071 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P071, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P071Input : RatPair2542 := (momentPanelPhase2622K04P071 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P071Expected : RatState2542 :=
  ((((11972690961326891934607110879706248472983180485610961313497786704581326790473359553 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7588831930935939945390301689877387 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P071_replay :
    compactExp2620 momentScalarAmp2622K04P071Input 20 = momentScalarAmp2622K04P071Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P071_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-37 / 200) 0) -
      (momentScalarAmp2622K04P071Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P071]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P071 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P071 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P071Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P071_replay] at h
  simpa only [momentPanelPhase_owner2622K04P071] using h

theorem momentScalarAmp2622K04P071_radius_le :
    (momentScalarAmp2622K04P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P071Expected]

def momentScalarGrow2622K04P071Input : RatPair2542 := (momentPanelGrowth2622K04P071 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P071Expected : RatState2542 :=
  ((((1327344266362568570686271623016566214476213770420425328759006500451908652644856674636009655093743 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3365216814226463646524188116279075805440588575447 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P071_replay :
    compactExp2620 momentScalarGrow2622K04P071Input 20 = momentScalarGrow2622K04P071Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P071_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P071Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P071]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P071 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P071 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P071Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P071_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P071] using h

theorem momentScalarGrow2622K04P071_radius_le :
    (momentScalarGrow2622K04P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P071Expected]

end ConnesWeilRH.Dev
