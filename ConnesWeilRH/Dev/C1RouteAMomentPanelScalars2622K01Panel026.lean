import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P026 : ℚ := ((-28612095312881398324712335070558946739106634662201147 : ℚ) / 567830494543066138679039072945481640009875744358400)

def momentPanelGrowth2622K01P026 : ℚ := ((1787075184196824658561242369212151542472991042682651 : ℚ) / 1619462275721135028039810632385105893875093025587200)

theorem momentPanelPhase_owner2622K01P026 :
    (momentPanelPhase2622K01P026 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-127 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P026 :
    (momentPanelGrowth2622K01P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P026Input : RatPair2542 := (momentPanelPhase2622K01P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P026Expected : RatState2542 :=
  ((((139683546994527283482586598401353341558993025164165736341278376321436764871 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((11142960447593733776529601 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K01P026_replay :
    compactExp2620 momentScalarAmp2622K01P026Input 20 = momentScalarAmp2622K01P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K01P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P026_replay] at h
  simpa only [momentPanelPhase_owner2622K01P026] using h

theorem momentScalarAmp2622K01P026_radius_le :
    (momentScalarAmp2622K01P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P026Expected]

def momentScalarGrow2622K01P026Input : RatPair2542 := (momentPanelGrowth2622K01P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P026Expected : RatState2542 :=
  ((((6439352324858856194705390837523685909735476305034162261926841950515532407102230655721368895926651 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8162840249284138401596373809181545131520068237993 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P026_replay :
    compactExp2620 momentScalarGrow2622K01P026Input 20 = momentScalarGrow2622K01P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P026] using h

theorem momentScalarGrow2622K01P026_radius_le :
    (momentScalarGrow2622K01P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P026Expected]

end ConnesWeilRH.Dev
