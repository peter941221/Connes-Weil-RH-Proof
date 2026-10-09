import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P139 : ℚ := ((-85436222136860100727524157174625372684699846294295627 : ℚ) / 2155072653601364122403958899570265181181128264908800)

def momentPanelGrowth2622K01P139 : ℚ := ((57289231412010938519374528698019637697662813779 : ℚ) / 107043576952946991079371447708712135228705996800)

theorem momentPanelPhase_owner2622K01P139 :
    (momentPanelPhase2622K01P139 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P139 :
    (momentPanelGrowth2622K01P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P139Input : RatPair2542 := (momentPanelPhase2622K01P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P139Expected : RatState2542 :=
  ((((12951587565518764414669111311465371475698281389471005407855376484276462618322487 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16418710910987286033140800196755 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P139_replay :
    compactExp2620 momentScalarAmp2622K01P139Input 20 = momentScalarAmp2622K01P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K01P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P139_replay] at h
  simpa only [momentPanelPhase_owner2622K01P139] using h

theorem momentScalarAmp2622K01P139_radius_le :
    (momentScalarAmp2622K01P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P139Expected]

def momentScalarGrow2622K01P139Input : RatPair2542 := (momentPanelGrowth2622K01P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P139Expected : RatState2542 :=
  ((((1823900034544094406386479100812486570827138435745293917234826717626852699417744331216281044089731 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4624133586924031278700692364515096993539953862009 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P139_replay :
    compactExp2620 momentScalarGrow2622K01P139Input 20 = momentScalarGrow2622K01P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P139] using h

theorem momentScalarGrow2622K01P139_radius_le :
    (momentScalarGrow2622K01P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P139Expected]

end ConnesWeilRH.Dev
