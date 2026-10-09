import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P056 : ℚ := ((-118807612183462195157900537831722817780120662388283641 : ℚ) / 3378866187712089422417386204074734785872514357657600)

def momentPanelGrowth2622K02P056 : ℚ := ((70166571771451468220115544811414893661488677837574253 : ℚ) / 232571010599821056790364439521973847120164030303436800)

theorem momentPanelPhase_owner2622K02P056 :
    (momentPanelPhase2622K02P056 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-67 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P056, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P056 :
    (momentPanelGrowth2622K02P056 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P056, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P056Input : RatPair2542 := (momentPanelPhase2622K02P056 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P056Expected : RatState2542 :=
  ((((572685804124878912654467010534909312347297401664367124687614268557595956166633477 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1451979697625575967312974801042309 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P056_replay :
    compactExp2620 momentScalarAmp2622K02P056Input 20 = momentScalarAmp2622K02P056Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P056_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-67 / 200) 0) -
      (momentScalarAmp2622K02P056Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P056]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P056 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P056 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P056Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P056_replay] at h
  simpa only [momentPanelPhase_owner2622K02P056] using h

theorem momentScalarAmp2622K02P056_radius_le :
    (momentScalarAmp2622K02P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P056Expected]

def momentScalarGrow2622K02P056Input : RatPair2542 := (momentPanelGrowth2622K02P056 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P056Expected : RatState2542 :=
  ((((1444092695651031777087862933293015378998964367774447033296846346699115242685119715528076137199865 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3661208891439858685606314285696789336645995816643 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P056_replay :
    compactExp2620 momentScalarGrow2622K02P056Input 20 = momentScalarGrow2622K02P056Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P056_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P056Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P056Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P056 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P056]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P056 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P056 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P056Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P056Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P056_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P056] using h

theorem momentScalarGrow2622K02P056_radius_le :
    (momentScalarGrow2622K02P056Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P056Expected]

end ConnesWeilRH.Dev
