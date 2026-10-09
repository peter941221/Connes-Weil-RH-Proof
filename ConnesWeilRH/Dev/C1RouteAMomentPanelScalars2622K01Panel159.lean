import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P159 : ℚ := ((-28481294713344372430364564517050567945365297882299329 : ℚ) / 491900917291109073006738259370768498754313623961600)

def momentPanelGrowth2622K01P159 : ℚ := ((50011273795098860844105461917623841291436134048691 : ℚ) / 30935593739401680421938348387817807081096033075200)

theorem momentPanelPhase_owner2622K01P159 :
    (momentPanelPhase2622K01P159 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (139 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P159 :
    (momentPanelGrowth2622K01P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P159Input : RatPair2542 := (momentPanelPhase2622K01P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P159Expected : RatState2542 :=
  ((((76333229227784441323001942373598267630848855838514799918164834964675297 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((81605939171022742515375 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K01P159_replay :
    compactExp2620 momentScalarAmp2622K01P159Input 20 = momentScalarAmp2622K01P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K01P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P159_replay] at h
  simpa only [momentPanelPhase_owner2622K01P159] using h

theorem momentScalarAmp2622K01P159_radius_le :
    (momentScalarAmp2622K01P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P159Expected]

def momentScalarGrow2622K01P159Input : RatPair2542 := (momentPanelGrowth2622K01P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P159Expected : RatState2542 :=
  ((((672311006650417144160524482786180029615125975123275876803794869642674347703332026192022374526579 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((13636066194719354631931426985688154306681190780479 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P159_replay :
    compactExp2620 momentScalarGrow2622K01P159Input 20 = momentScalarGrow2622K01P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P159] using h

theorem momentScalarGrow2622K01P159_radius_le :
    (momentScalarGrow2622K01P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P159Expected]

end ConnesWeilRH.Dev
