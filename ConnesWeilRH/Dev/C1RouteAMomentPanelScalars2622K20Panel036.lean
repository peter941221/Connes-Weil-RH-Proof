import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P036 : ℚ := ((-827290813143742960741058827875172194711 : ℚ) / 19302769219795294742470599048901427200)

def momentPanelGrowth2622K20P036 : ℚ := ((2102857103942353139090829283151408311729 : ℚ) / 3180729052984342441807777038538165452800)

theorem momentPanelPhase_owner2622K20P036 :
    (momentPanelPhase2622K20P036 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-107 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P036, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P036 :
    (momentPanelGrowth2622K20P036 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P036, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P036Input : RatPair2542 := (momentPanelPhase2622K20P036 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P036Expected : RatState2542 :=
  ((((130094610221859238626304152033672896170888979231991198777642036828581071598151 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((659687423676417122827313226571 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P036_replay :
    compactExp2620 momentScalarAmp2622K20P036Input 20 = momentScalarAmp2622K20P036Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P036_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-107 / 200) 0) -
      (momentScalarAmp2622K20P036Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P036]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P036 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P036 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P036Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P036_replay] at h
  simpa only [momentPanelPhase_owner2622K20P036] using h

theorem momentScalarAmp2622K20P036_radius_le :
    (momentScalarAmp2622K20P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P036Expected]

def momentScalarGrow2622K20P036Input : RatPair2542 := (momentPanelGrowth2622K20P036 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P036Expected : RatState2542 :=
  ((((4137340127067839301006794781005655789934636741722050007592580163436113993542938775401070565566817 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5244698388657112956114166719028706159755618255407 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K20P036_replay :
    compactExp2620 momentScalarGrow2622K20P036Input 20 = momentScalarGrow2622K20P036Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P036_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P036Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P036Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P036 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P036]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P036 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P036 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P036Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P036Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P036_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P036] using h

theorem momentScalarGrow2622K20P036_radius_le :
    (momentScalarGrow2622K20P036Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P036Expected]

end ConnesWeilRH.Dev
