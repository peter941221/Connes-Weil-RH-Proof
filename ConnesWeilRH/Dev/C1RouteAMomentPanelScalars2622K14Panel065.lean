import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P065 : ℚ := ((-820942134399932138523812183383229314173 : ℚ) / 25419943956256638542333090036763852800)

def momentPanelGrowth2622K14P065 : ℚ := ((2831748899223431679735235120090583 : ℚ) / 15211807202738752817960438464512000)

theorem momentPanelPhase_owner2622K14P065 :
    (momentPanelPhase2622K14P065 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-49 / 200) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P065, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P065 :
    (momentPanelGrowth2622K14P065 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (-49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P065, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P065Input : RatPair2542 := (momentPanelPhase2622K14P065 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P065Expected : RatState2542 :=
  ((((10067975322086369295282438316399939600333654666555052171735785262021380778172754189 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((25526136092613824025608208188708473 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K14P065_replay :
    compactExp2620 momentScalarAmp2622K14P065Input 20 = momentScalarAmp2622K14P065Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P065_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-49 / 200) 0) -
      (momentScalarAmp2622K14P065Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P065]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P065 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P065 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P065Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P065_replay] at h
  simpa only [momentPanelPhase_owner2622K14P065] using h

theorem momentScalarAmp2622K14P065_radius_le :
    (momentScalarAmp2622K14P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P065Expected]

def momentScalarGrow2622K14P065Input : RatPair2542 := (momentPanelGrowth2622K14P065 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P065Expected : RatState2542 :=
  ((((2573028264872024112530808633963680260245526430822095557041518669022234024038748222279148190237215 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1630850122658254863313067595580464188608494475267 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K14P065_replay :
    compactExp2620 momentScalarGrow2622K14P065Input 20 = momentScalarGrow2622K14P065Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P065_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P065Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P065]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P065 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P065 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P065Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P065_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P065] using h

theorem momentScalarGrow2622K14P065_radius_le :
    (momentScalarGrow2622K14P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P065Expected]

end ConnesWeilRH.Dev
