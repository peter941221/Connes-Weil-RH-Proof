import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P048 : ℚ := ((-73322793907616574973108447978325298553224129975178175 : ℚ) / 2016324196402646938526758687336201960992815934603264)

def momentPanelGrowth2622K03P048 : ℚ := ((145012952903171865144263099618007777877933578986107425 : ℚ) / 387250526433328352160567248643053765778372034576777216)

theorem momentPanelPhase_owner2622K03P048 :
    (momentPanelPhase2622K03P048 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-83 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P048, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P048 :
    (momentPanelGrowth2622K03P048 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P048, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P048Input : RatPair2542 := (momentPanelPhase2622K03P048 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P048Expected : RatState2542 :=
  ((((86020060417449501533368470808121026906926090063572152938238757675435980149661967 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((436188654044886445790748662009985 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P048_replay :
    compactExp2620 momentScalarAmp2622K03P048Input 20 = momentScalarAmp2622K03P048Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P048_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-83 / 200) 0) -
      (momentScalarAmp2622K03P048Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P048]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P048 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P048 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P048Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P048_replay] at h
  simpa only [momentPanelPhase_owner2622K03P048] using h

theorem momentScalarAmp2622K03P048_radius_le :
    (momentScalarAmp2622K03P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P048Expected]

def momentScalarGrow2622K03P048Input : RatPair2542 := (momentPanelGrowth2622K03P048 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P048Expected : RatState2542 :=
  ((((3106190048997925839509858838407605841724147493952179409439266102426998370084448466167831225120077 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3937562273850439349381112978290637405504922272395 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P048_replay :
    compactExp2620 momentScalarGrow2622K03P048Input 20 = momentScalarGrow2622K03P048Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P048_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P048Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P048Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P048 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P048]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P048 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P048 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P048Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P048Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P048_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P048] using h

theorem momentScalarGrow2622K03P048_radius_le :
    (momentScalarGrow2622K03P048Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P048Expected]

end ConnesWeilRH.Dev
