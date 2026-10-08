import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P103 : ℚ := ((-328208236517287978197491156353495386599270805064786941 : ℚ) / 11209888828051150097807989661250224700177368534220800)

def momentPanelGrowth2622K04P103 : ℚ := ((52042112797366093256290437178257192972436448814426109 : ℚ) / 285801640546982536514314273038562217726694948392140800)

theorem momentPanelPhase_owner2622K04P103 :
    (momentPanelPhase2622K04P103 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P103 :
    (momentPanelGrowth2622K04P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P103Input : RatPair2542 := (momentPanelPhase2622K04P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P103Expected : RatState2542 :=
  ((((102817432169685959350090072837610323519272126182848267341019243430039998747123913333 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((260680437855494123152810044328061537 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P103_replay :
    compactExp2620 momentScalarAmp2622K04P103Input 20 = momentScalarAmp2622K04P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K04P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P103_replay] at h
  simpa only [momentPanelPhase_owner2622K04P103] using h

theorem momentScalarAmp2622K04P103_radius_le :
    (momentScalarAmp2622K04P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P103Expected]

def momentScalarGrow2622K04P103Input : RatPair2542 := (momentPanelGrowth2622K04P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P103Expected : RatState2542 :=
  ((((2562595401110796801381013042616099515951596395331469652260528741786145801396217359962442060187591 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3248475034242328422117852707973072846039702976257 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P103_replay :
    compactExp2620 momentScalarGrow2622K04P103Input 20 = momentScalarGrow2622K04P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P103] using h

theorem momentScalarGrow2622K04P103_radius_le :
    (momentScalarGrow2622K04P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P103Expected]

end ConnesWeilRH.Dev
