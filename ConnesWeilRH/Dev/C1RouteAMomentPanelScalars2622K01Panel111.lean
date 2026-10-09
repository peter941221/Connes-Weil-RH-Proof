import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P111 : ℚ := ((-28508621727366649750256136087634802226015564028119137 : ℚ) / 907515445407084590370911133674461482468969440870400)

def momentPanelGrowth2622K01P111 : ℚ := ((9937672399147134249500986093092407528402792551879331 : ℚ) / 67314246323283762393271655520175917526436537381683200)

theorem momentPanelPhase_owner2622K01P111 :
    (momentPanelPhase2622K01P111 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (43 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P111 :
    (momentPanelGrowth2622K01P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P111Input : RatPair2542 := (momentPanelPhase2622K01P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P111Expected : RatState2542 :=
  ((((24303819497989895423132442666581345386981586651788574595594412898529065579080951149 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((15404837189096299349602228013903103 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P111_replay :
    compactExp2620 momentScalarAmp2622K01P111Input 20 = momentScalarAmp2622K01P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K01P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P111_replay] at h
  simpa only [momentPanelPhase_owner2622K01P111] using h

theorem momentScalarAmp2622K01P111_radius_le :
    (momentScalarAmp2622K01P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P111Expected]

def momentScalarGrow2622K01P111Input : RatPair2542 := (momentPanelGrowth2622K01P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P111Expected : RatState2542 :=
  ((((2475790885911050800513131049473978616661079397025316788441304813360837477719551394827667909768443 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3138437360698026274045965991388121357849378916963 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P111_replay :
    compactExp2620 momentScalarGrow2622K01P111Input 20 = momentScalarGrow2622K01P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P111] using h

theorem momentScalarGrow2622K01P111_radius_le :
    (momentScalarGrow2622K01P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P111Expected]

end ConnesWeilRH.Dev
