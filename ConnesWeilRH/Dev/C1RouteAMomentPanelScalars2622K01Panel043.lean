import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P043 : ℚ := ((-85828580482903755996133073441547940382495023691158539 : ℚ) / 2237282120701227411552916171410556101036774470451200)

def momentPanelGrowth2622K01P043 : ℚ := ((336747528367537446879276111865157281983760865831402971 : ℚ) / 721945663793648263158632506269667503245701783171891200)

theorem momentPanelPhase_owner2622K01P043 :
    (momentPanelPhase2622K01P043 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-93 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P043, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P043 :
    (momentPanelGrowth2622K01P043 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P043, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P043Input : RatPair2542 := (momentPanelPhase2622K01P043 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P043Expected : RatState2542 :=
  ((((23322897368281813155154670046689318446945206277942484434230441638281689637790715 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((59132735486117355716557040480733 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P043_replay :
    compactExp2620 momentScalarAmp2622K01P043Input 20 = momentScalarAmp2622K01P043Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P043_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-93 / 200) 0) -
      (momentScalarAmp2622K01P043Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P043]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P043 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P043 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P043Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P043_replay] at h
  simpa only [momentPanelPhase_owner2622K01P043] using h

theorem momentScalarAmp2622K01P043_radius_le :
    (momentScalarAmp2622K01P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P043Expected]

def momentScalarGrow2622K01P043Input : RatPair2542 := (momentPanelGrowth2622K01P043 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P043Expected : RatState2542 :=
  ((((1702718504103720588501693177351161858649359924673412779653220506467639547068411483896514174627829 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2158451173589652153473654777253389915607951866397 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P043_replay :
    compactExp2620 momentScalarGrow2622K01P043Input 20 = momentScalarGrow2622K01P043Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P043_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P043Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P043]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P043 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P043 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P043Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P043_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P043] using h

theorem momentScalarGrow2622K01P043_radius_le :
    (momentScalarGrow2622K01P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P043Expected]

end ConnesWeilRH.Dev
