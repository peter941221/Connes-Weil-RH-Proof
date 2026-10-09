import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P167 : ℚ := ((-6395873769136063824724561716888509333 : ℚ) / 86403064911556116006015290478428160)

def momentPanelGrowth2622K05P167 : ℚ := ((2980018910754590687229479675022700482249 : ℚ) / 971974647146675532639921373491023052800)

theorem momentPanelPhase_owner2622K05P167 :
    (momentPanelPhase2622K05P167 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P167 :
    (momentPanelGrowth2622K05P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P167Input : RatPair2542 := (momentPanelPhase2622K05P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P167Expected : RatState2542 :=
  ((((15188613397525418937578127527825284274873346055142535707006454639 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851658484472911292163 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P167_replay :
    compactExp2620 momentScalarAmp2622K05P167Input 20 = momentScalarAmp2622K05P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K05P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P167_replay] at h
  simpa only [momentPanelPhase_owner2622K05P167] using h

theorem momentScalarAmp2622K05P167_radius_le :
    (momentScalarAmp2622K05P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P167Expected]

def momentScalarGrow2622K05P167Input : RatPair2542 := (momentPanelGrowth2622K05P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P167Expected : RatState2542 :=
  ((((11456732369697473235213472634184509010654789281257150280251775715653805399299107315516441467875021 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((58092364803243887842531562303185465727425350021449 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P167_replay :
    compactExp2620 momentScalarGrow2622K05P167Input 20 = momentScalarGrow2622K05P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P167] using h

theorem momentScalarGrow2622K05P167_radius_le :
    (momentScalarGrow2622K05P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P167Expected]

end ConnesWeilRH.Dev
