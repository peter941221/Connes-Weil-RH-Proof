import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P024 : ℚ := ((-119999305781377191373898298372800648815511787903399737 : ℚ) / 2173127336914094514899346217083801294656370009702400)

def momentPanelGrowth2622K02P024 : ℚ := ((364861281859438924865780747541202336107107252430052359 : ℚ) / 284153740360984235235644376058235830642227429140070400)

theorem momentPanelPhase_owner2622K02P024 :
    (momentPanelPhase2622K02P024 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P024 :
    (momentPanelGrowth2622K02P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P024Input : RatPair2542 := (momentPanelPhase2622K02P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P024Expected : RatState2542 :=
  ((((2228508806782403405769586341338863403901242283266600449732587439376439113 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5242970937012267315793945 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P024_replay :
    compactExp2620 momentScalarAmp2622K02P024Input 20 = momentScalarAmp2622K02P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K02P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P024_replay] at h
  simpa only [momentPanelPhase_owner2622K02P024] using h

theorem momentScalarAmp2622K02P024_radius_le :
    (momentScalarAmp2622K02P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P024Expected]

def momentScalarGrow2622K02P024Input : RatPair2542 := (momentPanelGrowth2622K02P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P024Expected : RatState2542 :=
  ((((7713380750690674279019094770806702649467926998052938860690557609915671762217083135623853847863367 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((9777859764972459394688934644721221378791437678923 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P024_replay :
    compactExp2620 momentScalarGrow2622K02P024Input 20 = momentScalarGrow2622K02P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P024] using h

theorem momentScalarGrow2622K02P024_radius_le :
    (momentScalarGrow2622K02P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P024Expected]

end ConnesWeilRH.Dev
