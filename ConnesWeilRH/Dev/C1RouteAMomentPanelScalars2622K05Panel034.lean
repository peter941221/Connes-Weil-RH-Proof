import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P034 : ℚ := ((-2477858649256758379950694028028112469841 : ℚ) / 56139681541947458566443596834563686400)

def momentPanelGrowth2622K05P034 : ℚ := ((45245724379255631763871475771360386883 : ℚ) / 62213249097760951274894601232161177600)

theorem momentPanelPhase_owner2622K05P034 :
    (momentPanelPhase2622K05P034 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-111 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P034, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P034 :
    (momentPanelGrowth2622K05P034 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P034, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P034Input : RatPair2542 := (momentPanelPhase2622K05P034 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P034Expected : RatState2542 :=
  ((((72434681050008388991464338819323709663582039161113942223854161015390836304699 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((183653881893666471207478234157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P034_replay :
    compactExp2620 momentScalarAmp2622K05P034Input 20 = momentScalarAmp2622K05P034Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P034_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-111 / 200) 0) -
      (momentScalarAmp2622K05P034Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P034]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P034 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P034 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P034Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P034_replay] at h
  simpa only [momentPanelPhase_owner2622K05P034] using h

theorem momentScalarAmp2622K05P034_radius_le :
    (momentScalarAmp2622K05P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P034Expected]

def momentScalarGrow2622K05P034Input : RatPair2542 := (momentPanelGrowth2622K05P034 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P034Expected : RatState2542 :=
  ((((2210126997379167548746834312535050659630177062347528055196354903026594746425467645676136282905581 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5603333743271282694644193087617669236684098546865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P034_replay :
    compactExp2620 momentScalarGrow2622K05P034Input 20 = momentScalarGrow2622K05P034Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P034_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P034Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P034]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P034 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P034 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P034Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P034_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P034] using h

theorem momentScalarGrow2622K05P034_radius_le :
    (momentScalarGrow2622K05P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P034Expected]

end ConnesWeilRH.Dev
