import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P109 : ℚ := ((-92440773929159917228503246334698662925 : ℚ) / 3121787356555650504972265128938438656)

def momentPanelGrowth2622K07P109 : ℚ := ((25670756233415393744689314585425 : ℚ) / 121694457621910022543683507716096)

theorem momentPanelPhase_owner2622K07P109 :
    (momentPanelPhase2622K07P109 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (39 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P109, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P109 :
    (momentPanelGrowth2622K07P109 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P109, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P109Input : RatPair2542 := (momentPanelPhase2622K07P109 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P109Expected : RatState2542 :=
  ((((294775962530711593230228848077781284379314914539794689582025313309866235568900388187 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((186841739202026368095498722926026799 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P109_replay :
    compactExp2620 momentScalarAmp2622K07P109Input 20 = momentScalarAmp2622K07P109Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P109_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (39 / 200) 0) -
      (momentScalarAmp2622K07P109Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P109]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P109 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P109 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P109Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P109_replay] at h
  simpa only [momentPanelPhase_owner2622K07P109] using h

theorem momentScalarAmp2622K07P109_radius_le :
    (momentScalarAmp2622K07P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P109Expected]

def momentScalarGrow2622K07P109Input : RatPair2542 := (momentPanelGrowth2622K07P109 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P109Expected : RatState2542 :=
  ((((1318804974934531421495974102931524283805259736728241802002953097735576358839034218783624398410761 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3343567163486661621285227041782356512123806527871 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P109_replay :
    compactExp2620 momentScalarGrow2622K07P109Input 20 = momentScalarGrow2622K07P109Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P109_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P109Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P109]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P109 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P109 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P109Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P109_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P109] using h

theorem momentScalarGrow2622K07P109_radius_le :
    (momentScalarGrow2622K07P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P109Expected]

end ConnesWeilRH.Dev
