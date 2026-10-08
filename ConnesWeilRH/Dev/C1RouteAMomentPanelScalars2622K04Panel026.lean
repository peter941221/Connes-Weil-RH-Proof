import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P026 : ℚ := ((-127838227336222905975622376665434167360605662128496053 : ℚ) / 2271321978172264554716156291781926560039502977433600)

def momentPanelGrowth2622K04P026 : ℚ := ((7749687664205396234100786820191341968712670622804949 : ℚ) / 6477849102884540112159242529540423575500372102348800)

theorem momentPanelPhase_owner2622K04P026 :
    (momentPanelPhase2622K04P026 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-127 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P026 :
    (momentPanelGrowth2622K04P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P026Input : RatPair2542 := (momentPanelPhase2622K04P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P026Expected : RatState2542 :=
  ((((769010408887855914715086966438468684078160457460355453001594495962255065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3392740472607714418663471 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P026_replay :
    compactExp2620 momentScalarAmp2622K04P026Input 20 = momentScalarAmp2622K04P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K04P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P026_replay] at h
  simpa only [momentPanelPhase_owner2622K04P026] using h

theorem momentScalarAmp2622K04P026_radius_le :
    (momentScalarAmp2622K04P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P026Expected]

def momentScalarGrow2622K04P026Input : RatPair2542 := (momentPanelGrowth2622K04P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P026Expected : RatState2542 :=
  ((((3532897033797002516268807435007952012453627316509281868562966687400193373299964046259860298492777 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((8956947871748615401341800622697106211549965098381 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P026_replay :
    compactExp2620 momentScalarGrow2622K04P026Input 20 = momentScalarGrow2622K04P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P026] using h

theorem momentScalarGrow2622K04P026_radius_le :
    (momentScalarGrow2622K04P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P026Expected]

end ConnesWeilRH.Dev
