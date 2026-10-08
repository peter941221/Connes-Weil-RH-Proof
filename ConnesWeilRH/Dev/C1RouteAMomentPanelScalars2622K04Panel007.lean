import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P007 : ℚ := ((-2968235323911599345135603657477439571769397128580801 : ℚ) / 29172942838909819968831365215547680587663340994560)

def momentPanelGrowth2622K04P007 : ℚ := ((2412835126100586368793775622673541961094856165187204389 : ℚ) / 460445377217254611400130377404280240595033356291276800)

theorem momentPanelPhase_owner2622K04P007 :
    (momentPanelPhase2622K04P007 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P007, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P007 :
    (momentPanelGrowth2622K04P007 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P007, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P007Input : RatPair2542 := (momentPanelPhase2622K04P007 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P007Expected : RatState2542 :=
  ((((13861065129907314535064484526587968197773265783648785 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349430315 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P007_replay :
    compactExp2620 momentScalarAmp2622K04P007Input 20 = momentScalarAmp2622K04P007Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P007_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 40) 0) -
      (momentScalarAmp2622K04P007Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P007]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P007 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P007 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P007Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P007_replay] at h
  simpa only [momentPanelPhase_owner2622K04P007] using h

theorem momentScalarAmp2622K04P007_radius_le :
    (momentScalarAmp2622K04P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P007Expected]

def momentScalarGrow2622K04P007Input : RatPair2542 := (momentPanelGrowth2622K04P007 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P007Expected : RatState2542 :=
  ((((403085606957724752977842121350772748637814735915813462839129137559391414164353925353518313238620381 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((255484579023653840670560838831290203893606911068471 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P007_replay :
    compactExp2620 momentScalarGrow2622K04P007Input 20 = momentScalarGrow2622K04P007Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P007_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P007Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P007]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P007 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P007 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P007Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P007_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P007] using h

theorem momentScalarGrow2622K04P007_radius_le :
    (momentScalarGrow2622K04P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P007Expected]

end ConnesWeilRH.Dev
