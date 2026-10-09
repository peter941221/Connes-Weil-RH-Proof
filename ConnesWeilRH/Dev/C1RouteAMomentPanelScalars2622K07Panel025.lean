import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P025 : ℚ := ((-107224283902083050189792006278389164325 : ℚ) / 1895107223726797477731935371160190976)

def momentPanelGrowth2622K07P025 : ℚ := ((902001398110414707630044183366821625 : ℚ) / 721526439240304523661499517248733184)

theorem momentPanelPhase_owner2622K07P025 :
    (momentPanelPhase2622K07P025 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-129 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P025, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P025 :
    (momentPanelGrowth2622K07P025 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P025, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P025Input : RatPair2542 := (momentPanelPhase2622K07P025 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P025Expected : RatState2542 :=
  ((((572030437512286407341941950567549134329484381907511944952485656730714027 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3143025494893559207622685 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P025_replay :
    compactExp2620 momentScalarAmp2622K07P025Input 20 = momentScalarAmp2622K07P025Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P025_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-129 / 200) 0) -
      (momentScalarAmp2622K07P025Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P025]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P025 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P025 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P025Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P025_replay] at h
  simpa only [momentPanelPhase_owner2622K07P025] using h

theorem momentScalarAmp2622K07P025_radius_le :
    (momentScalarAmp2622K07P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P025Expected]

def momentScalarGrow2622K07P025Input : RatPair2542 := (momentPanelGrowth2622K07P025 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P025Expected : RatState2542 :=
  ((((932036489964887291028536544229430082005891952055432694165816560790756053922187928545073805224853 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9451961658719534666530202723749611314537004489879 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P025_replay :
    compactExp2620 momentScalarGrow2622K07P025Input 20 = momentScalarGrow2622K07P025Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P025_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P025Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P025Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P025 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P025]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P025 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P025 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P025Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P025Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P025_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P025] using h

theorem momentScalarGrow2622K07P025_radius_le :
    (momentScalarGrow2622K07P025Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P025Expected]

end ConnesWeilRH.Dev
