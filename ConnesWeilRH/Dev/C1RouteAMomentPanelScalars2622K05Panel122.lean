import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P122 : ℚ := ((-6401626898959031146517277239415227111 : ℚ) / 193494187618836935844456777268592640)

def momentPanelGrowth2622K05P122 : ℚ := ((21215984941011390386011129910544576987969 : ℚ) / 80527170733860292660099597189226745036800)

theorem momentPanelPhase_owner2622K05P122 :
    (momentPanelPhase2622K05P122 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P122 :
    (momentPanelGrowth2622K05P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P122Input : RatPair2542 := (momentPanelPhase2622K05P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P122Expected : RatState2542 :=
  ((((2286618174462524161769164456775075915404906247174999919034924547253160481782422117 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((11594897440568884490410199549307017 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P122_replay :
    compactExp2620 momentScalarAmp2622K05P122Input 20 = momentScalarAmp2622K05P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K05P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P122_replay] at h
  simpa only [momentPanelPhase_owner2622K05P122] using h

theorem momentScalarAmp2622K05P122_radius_le :
    (momentScalarAmp2622K05P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P122Expected]

def momentScalarGrow2622K05P122Input : RatPair2542 := (momentPanelGrowth2622K05P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P122Expected : RatState2542 :=
  ((((2779837670889443344677261604449461984534687351276675853852884947184065477845966843462727852511179 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3523862006639486292630248486615007075575317510927 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P122_replay :
    compactExp2620 momentScalarGrow2622K05P122Input 20 = momentScalarGrow2622K05P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P122] using h

theorem momentScalarGrow2622K05P122_radius_le :
    (momentScalarGrow2622K05P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P122Expected]

end ConnesWeilRH.Dev
