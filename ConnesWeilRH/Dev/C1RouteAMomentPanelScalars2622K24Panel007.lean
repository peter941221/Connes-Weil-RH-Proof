import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P007 : ℚ := ((-19735975267830158891350720569926577447 : ℚ) / 207286226149320071732740908143083520)

def momentPanelGrowth2622K24P007 : ℚ := ((16885071459386113047070737447858909488483 : ℚ) / 3271661179960393975819459750228760985600)

theorem momentPanelPhase_owner2622K24P007 :
    (momentPanelPhase2622K24P007 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 40) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P007, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P007 :
    (momentPanelGrowth2622K24P007 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P007, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P007Input : RatPair2542 := (momentPanelPhase2622K24P007 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P007Expected : RatState2542 :=
  ((((4773748190314693269606839325425695862559163328509828311 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258361526565 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K24P007_replay :
    compactExp2620 momentScalarAmp2622K24P007Input 20 = momentScalarAmp2622K24P007Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P007_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 40) 0) -
      (momentScalarAmp2622K24P007Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P007]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P007 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P007 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P007Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P007_replay] at h
  simpa only [momentPanelPhase_owner2622K24P007] using h

theorem momentScalarAmp2622K24P007_radius_le :
    (momentScalarAmp2622K24P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P007Expected]

def momentScalarGrow2622K24P007Input : RatPair2542 := (momentPanelGrowth2622K24P007 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P007Expected : RatState2542 :=
  ((((372388417868921725580387854373706681816707218648089486991972554092920900478912204834724091118366797 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((472056078000977114191070848782604263131470626889339 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K24P007_replay :
    compactExp2620 momentScalarGrow2622K24P007Input 20 = momentScalarGrow2622K24P007Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P007_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P007Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P007]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P007 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P007 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P007Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P007_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P007] using h

theorem momentScalarGrow2622K24P007_radius_le :
    (momentScalarGrow2622K24P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P007Expected]

end ConnesWeilRH.Dev
