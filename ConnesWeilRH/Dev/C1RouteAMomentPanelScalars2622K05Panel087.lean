import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P087 : ℚ := ((-6497998979127841954855949698855320437 : ℚ) / 216210486374926806719277698708930560)

def momentPanelGrowth2622K05P087 : ℚ := ((3253968816896097407065522935577990408209 : ℚ) / 101229588475584381875185948154873564364800)

theorem momentPanelPhase_owner2622K05P087 :
    (momentPanelPhase2622K05P087 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P087 :
    (momentPanelGrowth2622K05P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P087Input : RatPair2542 := (momentPanelPhase2622K05P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P087Expected : RatState2542 :=
  ((((47340641716051365129325374598203100273069860886543461189125368591246901979263198187 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((240052451777594102264647279957201517 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P087_replay :
    compactExp2620 momentScalarAmp2622K05P087Input 20 = momentScalarAmp2622K05P087Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622K05P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P087]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P087 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P087_replay] at h
  simpa only [momentPanelPhase_owner2622K05P087] using h

theorem momentScalarAmp2622K05P087_radius_le :
    (momentScalarAmp2622K05P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P087Expected]

def momentScalarGrow2622K05P087Input : RatPair2542 := (momentPanelGrowth2622K05P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P087Expected : RatState2542 :=
  ((((2205762591397874869994117618577326874588697043670935918723838861811408817945072557175377158832019 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2796136187230010701254279507218378767936212201723 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P087_replay :
    compactExp2620 momentScalarGrow2622K05P087Input 20 = momentScalarGrow2622K05P087Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P087_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P087] using h

theorem momentScalarGrow2622K05P087_radius_le :
    (momentScalarGrow2622K05P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P087Expected]

end ConnesWeilRH.Dev
