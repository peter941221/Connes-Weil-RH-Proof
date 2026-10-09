import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P103 : ℚ := ((-58939683 : ℚ) / 1963550)

def momentPanelGrowth2622K06P103 : ℚ := ((6377467 : ℚ) / 50061675)

theorem momentPanelPhase_owner2622K06P103 :
    (momentPanelPhase2622K06P103 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P103 :
    (momentPanelGrowth2622K06P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P103Input : RatPair2542 := (momentPanelPhase2622K06P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P103Expected : RatState2542 :=
  ((((196528164809100409284488950800965665077431843195448236969483152664001717277243006111 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((249136177840801879417475928010629949 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P103_replay :
    compactExp2620 momentScalarAmp2622K06P103Input 20 = momentScalarAmp2622K06P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K06P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P103_replay] at h
  simpa only [momentPanelPhase_owner2622K06P103] using h

theorem momentScalarAmp2622K06P103_radius_le :
    (momentScalarAmp2622K06P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P103Expected]

def momentScalarGrow2622K06P103Input : RatPair2542 := (momentPanelGrowth2622K06P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P103Expected : RatState2542 :=
  ((((37909178103714039019770795645868736935162506501608121613044671079048584301831844473522511122299 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((3075557538497673627635054540839354634161436940529 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P103_replay :
    compactExp2620 momentScalarGrow2622K06P103Input 20 = momentScalarGrow2622K06P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P103] using h

theorem momentScalarGrow2622K06P103_radius_le :
    (momentScalarGrow2622K06P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P103Expected]

end ConnesWeilRH.Dev
