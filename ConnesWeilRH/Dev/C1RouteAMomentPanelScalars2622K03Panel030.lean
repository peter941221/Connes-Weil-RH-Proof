import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P030 : ℚ := ((-73352234743734837542991061760168893321400248199338475 : ℚ) / 1573489200291383354311042183023168206037068374081536)

def momentPanelGrowth2622K03P030 : ℚ := ((80553089747649206624516404785204283722276386025 : ℚ) / 91343852333181432387730302044767688728495783936)

theorem momentPanelPhase_owner2622K03P030 :
    (momentPanelPhase2622K03P030 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-119 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P030, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P030 :
    (momentPanelGrowth2622K03P030 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P030, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P030Input : RatPair2542 := (momentPanelPhase2622K03P030 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P030Expected : RatState2542 :=
  ((((12129627492237651439221435075500899260798709032415592845361833089855968224399 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15379231029487569163173310131 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P030_replay :
    compactExp2620 momentScalarAmp2622K03P030Input 20 = momentScalarAmp2622K03P030Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P030_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-119 / 200) 0) -
      (momentScalarAmp2622K03P030Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P030]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P030 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P030 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P030Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P030_replay] at h
  simpa only [momentPanelPhase_owner2622K03P030] using h

theorem momentScalarAmp2622K03P030_radius_le :
    (momentScalarAmp2622K03P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P030Expected]

def momentScalarGrow2622K03P030Input : RatPair2542 := (momentPanelGrowth2622K03P030 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P030Expected : RatState2542 :=
  ((((5159271677470302865812275071919854952858905437878742078720824710091846399342817194396624972797513 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6540148338330387122183894652400439885491268025251 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P030_replay :
    compactExp2620 momentScalarGrow2622K03P030Input 20 = momentScalarGrow2622K03P030Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P030_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P030Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P030Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P030 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P030]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P030 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P030 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P030Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P030Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P030_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P030] using h

theorem momentScalarGrow2622K03P030_radius_le :
    (momentScalarGrow2622K03P030Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P030Expected]

end ConnesWeilRH.Dev
