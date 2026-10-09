import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P077 : ℚ := ((-117062094678765189196663391594229487280366719861205 : ℚ) / 3836441797993620160284672685880242926596822925312)

def momentPanelGrowth2622K03P077 : ℚ := ((246205499605548525949886265060788270019041035401535475 : ℚ) / 2942750628066159330730975916240718231635012403993772032)

theorem momentPanelPhase_owner2622K03P077 :
    (momentPanelPhase2622K03P077 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P077 :
    (momentPanelGrowth2622K03P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P077Input : RatPair2542 := (momentPanelPhase2622K03P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P077Expected : RatState2542 :=
  ((((59821407982715825237437756118270390995039671658182060744191041880184371516709740205 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((151669700944972689510741840508053975 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P077_replay :
    compactExp2620 momentScalarAmp2622K03P077Input 20 = momentScalarAmp2622K03P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K03P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P077_replay] at h
  simpa only [momentPanelPhase_owner2622K03P077] using h

theorem momentScalarAmp2622K03P077_radius_le :
    (momentScalarAmp2622K03P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P077Expected]

def momentScalarGrow2622K03P077Input : RatPair2542 := (momentPanelGrowth2622K03P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P077Expected : RatState2542 :=
  ((((2322383300150501180706651488570060775906125521130717480928462594891478684392707057202286162182399 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2943970349498607558239508254753859390005117070711 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P077_replay :
    compactExp2620 momentScalarGrow2622K03P077Input 20 = momentScalarGrow2622K03P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P077] using h

theorem momentScalarGrow2622K03P077_radius_le :
    (momentScalarGrow2622K03P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P077Expected]

end ConnesWeilRH.Dev
