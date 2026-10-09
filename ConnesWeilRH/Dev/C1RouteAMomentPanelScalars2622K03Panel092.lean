import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P092 : ℚ := ((-2922282639919023499172927127787785003480374628299375 : ℚ) / 97372546587171406925320501979722356184576505675776)

def momentPanelGrowth2622K03P092 : ℚ := ((191410986130663564456027150640278734256613174166262425 : ℚ) / 9117950738750209568639262156263176315061236160650018816)

theorem momentPanelPhase_owner2622K03P092 :
    (momentPanelPhase2622K03P092 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (1 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P092, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P092 :
    (momentPanelGrowth2622K03P092 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P092, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P092Input : RatPair2542 := (momentPanelPhase2622K03P092 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P092Expected : RatState2542 :=
  ((((98809834574331909817290476092764107668620455811835333627049127532181299583566655993 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((250519862258057895052534267226670481 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P092_replay :
    compactExp2620 momentScalarAmp2622K03P092Input 20 = momentScalarAmp2622K03P092Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P092_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (1 / 40) 0) -
      (momentScalarAmp2622K03P092Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P092]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P092 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P092 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P092Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P092_replay] at h
  simpa only [momentPanelPhase_owner2622K03P092] using h

theorem momentScalarAmp2622K03P092_radius_le :
    (momentScalarAmp2622K03P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P092Expected]

def momentScalarGrow2622K03P092Input : RatPair2542 := (momentPanelGrowth2622K03P092 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P092Expected : RatState2542 :=
  ((((2181301278688636010455703695864224722090263072271475900082680747448714363590549640604236520032053 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1382563909924838145073994557929940096568364103659 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P092_replay :
    compactExp2620 momentScalarGrow2622K03P092Input 20 = momentScalarGrow2622K03P092Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P092_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P092Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P092Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P092 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P092]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P092 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P092 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P092Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P092Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P092_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P092] using h

theorem momentScalarGrow2622K03P092_radius_le :
    (momentScalarGrow2622K03P092Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P092Expected]

end ConnesWeilRH.Dev
