import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K11
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K11P134 : ℚ := ((-796348680916311269347431333051916726187 : ℚ) / 21687980589184731184326795800136908800)

def momentPanelGrowth2622K11P134 : ℚ := ((45408334038767230382932152282904874809 : ℚ) / 103197914183859881700564811905813708800)

theorem momentPanelPhase_owner2622K11P134 :
    (momentPanelPhase2622K11P134 : ℝ) = momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (89 / 200) 0 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P134, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K11P134 :
    (momentPanelGrowth2622K11P134 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2))
      (89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P134, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K11P134Input : RatPair2542 := (momentPanelPhase2622K11P134 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K11P134Expected : RatState2542 :=
  ((((241537963923586395171449246106269798914855639035432721100670679401701545648524993 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((306196469388286740721315464496295 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K11P134_replay :
    compactExp2620 momentScalarAmp2622K11P134Input 20 = momentScalarAmp2622K11P134Expected := by
  decide +kernel

theorem momentScalarAmp2622K11P134_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (89 / 200) 0) -
      (momentScalarAmp2622K11P134Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K11P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K11P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P134]
  have h := compactExp_real_error2620 momentPanelPhase2622K11P134 20 hsmall
  change |Real.exp (momentPanelPhase2622K11P134 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K11P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K11P134Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K11P134_replay] at h
  simpa only [momentPanelPhase_owner2622K11P134] using h

theorem momentScalarAmp2622K11P134_radius_le :
    (momentScalarAmp2622K11P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarAmp2622K11P134Expected]

def momentScalarGrow2622K11P134Input : RatPair2542 := (momentPanelGrowth2622K11P134 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K11P134Expected : RatState2542 :=
  ((((829150679924611588726219283244418397816922300801478631314162164372106576673458657712065864321501 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4204291664104317049934974833430979797384655270933 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K11P134_replay :
    compactExp2620 momentScalarGrow2622K11P134Input 20 = momentScalarGrow2622K11P134Expected := by
  decide +kernel

theorem momentScalarGrow2622K11P134_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K11P134Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K11P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K11P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P134]
  have h := compactExp_real_error2620 momentPanelGrowth2622K11P134 20 hsmall
  change |Real.exp (momentPanelGrowth2622K11P134 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K11P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K11P134Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K11P134_replay] at h
  simpa only [momentPanelGrowth_owner2622K11P134] using h

theorem momentScalarGrow2622K11P134_radius_le :
    (momentScalarGrow2622K11P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarGrow2622K11P134Expected]

end ConnesWeilRH.Dev
