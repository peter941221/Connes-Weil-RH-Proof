import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P043 : ℚ := ((-106904417173910856585978984322173831225 : ℚ) / 2543495293936334077844681100271550464)

def momentPanelGrowth2622K07P043 : ℚ := ((447573953463170880911447407562538154025 : ℚ) / 820757195235328553233821942592007307264)

theorem momentPanelPhase_owner2622K07P043 :
    (momentPanelPhase2622K07P043 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-93 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P043, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P043 :
    (momentPanelGrowth2622K07P043 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-93 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P043, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P043Input : RatPair2542 := (momentPanelPhase2622K07P043 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P043Expected : RatState2542 :=
  ((((1191181293375114426818420638523111209332343312469536450671239310394603179011877 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((755032313313982760986759289503 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P043_replay :
    compactExp2620 momentScalarAmp2622K07P043Input 20 = momentScalarAmp2622K07P043Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P043_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-93 / 200) 0) -
      (momentScalarAmp2622K07P043Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P043]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P043 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P043 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P043Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P043_replay] at h
  simpa only [momentPanelPhase_owner2622K07P043] using h

theorem momentScalarAmp2622K07P043_radius_le :
    (momentScalarAmp2622K07P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P043Expected]

def momentScalarGrow2622K07P043Input : RatPair2542 := (momentPanelGrowth2622K07P043 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P043Expected : RatState2542 :=
  ((((1842457012785358244286598473938859531209258135704616265122589331069683955487011745643185620795085 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4671181047027321279340075430382030928323839479051 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P043_replay :
    compactExp2620 momentScalarGrow2622K07P043Input 20 = momentScalarGrow2622K07P043Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P043_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-93 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P043Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P043Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P043 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P043]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P043 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P043 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P043Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P043Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P043_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P043] using h

theorem momentScalarGrow2622K07P043_radius_le :
    (momentScalarGrow2622K07P043Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P043Expected]

end ConnesWeilRH.Dev
