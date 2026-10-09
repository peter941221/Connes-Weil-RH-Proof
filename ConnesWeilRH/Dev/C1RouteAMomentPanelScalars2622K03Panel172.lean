import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P172 : ℚ := ((-8746210455003168817318911037003246697248121360302125 : ℚ) / 93353417084511423900260368689752577880522691182592)

def momentPanelGrowth2622K03P172 : ℚ := ((1517180310752625397759548421745617033704745655313711475 : ℚ) / 294685041419042951296083441538739353980821348026417152)

theorem momentPanelPhase_owner2622K03P172 :
    (momentPanelPhase2622K03P172 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P172, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P172 :
    (momentPanelGrowth2622K03P172 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P172, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P172Input : RatPair2542 := (momentPanelPhase2622K03P172 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P172Expected : RatState2542 :=
  ((((43740102604446340339970099501588694141884477337455300871 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258404886357 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P172_replay :
    compactExp2620 momentScalarAmp2622K03P172Input 20 = momentScalarAmp2622K03P172Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P172_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 40) 0) -
      (momentScalarAmp2622K03P172Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P172]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P172 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P172 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P172Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P172_replay] at h
  simpa only [momentPanelPhase_owner2622K03P172] using h

theorem momentScalarAmp2622K03P172_radius_le :
    (momentScalarAmp2622K03P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P172Expected]

def momentScalarGrow2622K03P172Input : RatPair2542 := (momentPanelGrowth2622K03P172 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P172Expected : RatState2542 :=
  ((((367752355122312350339169356748428873508283520519959603787000626245443102699636955132484582376996393 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((233089602386371785555836610597997988193592280153219 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P172_replay :
    compactExp2620 momentScalarGrow2622K03P172Input 20 = momentScalarGrow2622K03P172Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P172_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P172Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P172Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P172 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P172]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P172 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P172 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P172Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P172Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P172_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P172] using h

theorem momentScalarGrow2622K03P172_radius_le :
    (momentScalarGrow2622K03P172Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P172Expected]

end ConnesWeilRH.Dev
