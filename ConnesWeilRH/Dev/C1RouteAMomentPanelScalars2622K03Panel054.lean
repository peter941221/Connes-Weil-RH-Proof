import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P054 : ℚ := ((-73298806640538625415362508530147724021689474996773275 : ℚ) / 2128859822477126463228442419455355753506322740412416)

def momentPanelGrowth2622K03P054 : ℚ := ((7604649137023445708299784609079504693184241154825 : ℚ) / 26398373324289433960054057290937862042535281557504)

theorem momentPanelPhase_owner2622K03P054 :
    (momentPanelPhase2622K03P054 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-71 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P054, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P054 :
    (momentPanelGrowth2622K03P054 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-71 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P054, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P054Input : RatPair2542 := (momentPanelPhase2622K03P054 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P054Expected : RatState2542 :=
  ((((1189510706438636606827839138412642760533191350055004181309470557898543339790237423 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((753966737928860799083807358535221 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P054_replay :
    compactExp2620 momentScalarAmp2622K03P054Input 20 = momentScalarAmp2622K03P054Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P054_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-71 / 200) 0) -
      (momentScalarAmp2622K03P054Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P054]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P054 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P054 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P054Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P054_replay] at h
  simpa only [momentPanelPhase_owner2622K03P054] using h

theorem momentScalarAmp2622K03P054_radius_le :
    (momentScalarAmp2622K03P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P054Expected]

def momentScalarGrow2622K03P054Input : RatPair2542 := (momentPanelGrowth2622K03P054 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P054Expected : RatState2542 :=
  ((((2849095265945865770635288000440846051270125504218364115946067821630552643140431717330431018252019 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3611656331762306412323548618284182733025558951597 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P054_replay :
    compactExp2620 momentScalarGrow2622K03P054Input 20 = momentScalarGrow2622K03P054Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P054_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-71 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P054Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P054Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P054 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P054]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P054 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P054 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P054Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P054Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P054_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P054] using h

theorem momentScalarGrow2622K03P054_radius_le :
    (momentScalarGrow2622K03P054Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P054Expected]

end ConnesWeilRH.Dev
