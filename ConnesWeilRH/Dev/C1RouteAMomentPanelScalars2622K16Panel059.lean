import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K16
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K16P059 : ℚ := ((-822882791177657854749546163934652846337 : ℚ) / 24527517933695965043679410980179148800)

def momentPanelGrowth2622K16P059 : ℚ := ((6715311153680048381374809100594514588083 : ℚ) / 27619071316375932186134219138988087705600)

theorem momentPanelPhase_owner2622K16P059 :
    (momentPanelPhase2622K16P059 : ℝ) = momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-61 / 200) 0 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P059, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K16P059 :
    (momentPanelGrowth2622K16P059 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2))
      (-61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P059, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K16P059Input : RatPair2542 := (momentPanelPhase2622K16P059 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K16P059Expected : RatState2542 :=
  ((((5745026707712343547579201900086231843284466506538140441221744315690198320621268845 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7282919571321606068149230950597551 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K16P059_replay :
    compactExp2620 momentScalarAmp2622K16P059Input 20 = momentScalarAmp2622K16P059Expected := by
  decide +kernel

theorem momentScalarAmp2622K16P059_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-61 / 200) 0) -
      (momentScalarAmp2622K16P059Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K16P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K16P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelPhase2622K16P059]
  have h := compactExp_real_error2620 momentPanelPhase2622K16P059 20 hsmall
  change |Real.exp (momentPanelPhase2622K16P059 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K16P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K16P059Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K16P059_replay] at h
  simpa only [momentPanelPhase_owner2622K16P059] using h

theorem momentScalarAmp2622K16P059_radius_le :
    (momentScalarAmp2622K16P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarAmp2622K16P059Expected]

def momentScalarGrow2622K16P059Input : RatPair2542 := (momentPanelGrowth2622K16P059 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K16P059Expected : RatState2542 :=
  ((((340489046667333731314489748056543151181647866176343589430869774491101876611721767464321284649865 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3452968354368783233176753033968568372788211110523 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K16P059_replay :
    compactExp2620 momentScalarGrow2622K16P059Input 20 = momentScalarGrow2622K16P059Expected := by
  decide +kernel

theorem momentScalarGrow2622K16P059_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 16).re * (storedWidth 16 ^ 2)) (-61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K16P059Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K16P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K16P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentPanelGrowth2622K16P059]
  have h := compactExp_real_error2620 momentPanelGrowth2622K16P059 20 hsmall
  change |Real.exp (momentPanelGrowth2622K16P059 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K16P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K16P059Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K16P059_replay] at h
  simpa only [momentPanelGrowth_owner2622K16P059] using h

theorem momentScalarGrow2622K16P059_radius_le :
    (momentScalarGrow2622K16P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, momentScalarGrow2622K16P059Expected]

end ConnesWeilRH.Dev
