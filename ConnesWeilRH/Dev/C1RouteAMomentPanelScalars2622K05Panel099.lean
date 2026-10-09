import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P099 : ℚ := ((-807703583194160157171581957451175029817 : ℚ) / 26799147809304952131161503124212940800)

def momentPanelGrowth2622K05P099 : ℚ := ((249579009299288446271317319066097763 : ℚ) / 3313131608756500363751783497570713600)

theorem momentPanelPhase_owner2622K05P099 :
    (momentPanelPhase2622K05P099 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P099, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P099 :
    (momentPanelGrowth2622K05P099 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P099, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P099Input : RatPair2542 := (momentPanelPhase2622K05P099 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P099Expected : RatState2542 :=
  ((((86956352186817758662804515984034886728262220586486902255743258038913804927314878103 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((220466880863120554582553654379992807 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P099_replay :
    compactExp2620 momentScalarAmp2622K05P099Input 20 = momentScalarAmp2622K05P099Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P099_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 200) 0) -
      (momentScalarAmp2622K05P099Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P099]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P099 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P099 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P099Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P099_replay] at h
  simpa only [momentPanelPhase_owner2622K05P099] using h

theorem momentScalarAmp2622K05P099_radius_le :
    (momentScalarAmp2622K05P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P099Expected]

def momentScalarGrow2622K05P099Input : RatPair2542 := (momentPanelGrowth2622K05P099 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P099Expected : RatState2542 :=
  ((((1151553515999256912176544509509475254129398295058131324031063849457104526202037046545057400059683 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((729883700440467984086763370124527936110857645869 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P099_replay :
    compactExp2620 momentScalarGrow2622K05P099Input 20 = momentScalarGrow2622K05P099Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P099_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P099Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P099]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P099 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P099 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P099Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P099_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P099] using h

theorem momentScalarGrow2622K05P099_radius_le :
    (momentScalarGrow2622K05P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P099Expected]

end ConnesWeilRH.Dev
