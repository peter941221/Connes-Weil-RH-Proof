import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P076 : ℚ := ((-356870655981572764710486108982262278864447574455213059 : ℚ) / 11209888828051150097807989661250224700177368534220800)

def momentPanelGrowth2622K04P076 : ℚ := ((52042112797366093256290437178257192972436448814426109 : ℚ) / 285801640546982536514314273038562217726694948392140800)

theorem momentPanelPhase_owner2622K04P076 :
    (momentPanelPhase2622K04P076 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P076 :
    (momentPanelGrowth2622K04P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P076Input : RatPair2542 := (momentPanelPhase2622K04P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P076Expected : RatState2542 :=
  ((((31892224480917541595171401997948774484460296770099992547264123854537336644191054523 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((40429424949169983236879515704177295 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P076_replay :
    compactExp2620 momentScalarAmp2622K04P076Input 20 = momentScalarAmp2622K04P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K04P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P076_replay] at h
  simpa only [momentPanelPhase_owner2622K04P076] using h

theorem momentScalarAmp2622K04P076_radius_le :
    (momentScalarAmp2622K04P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P076Expected]

def momentScalarGrow2622K04P076Input : RatPair2542 := (momentPanelGrowth2622K04P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P076Expected : RatState2542 :=
  ((((2562595401110796801381013042616099515951596395331469652260528741786145801396217359962442060187591 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3248475034242328422117852707973072846039702976257 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P076_replay :
    compactExp2620 momentScalarGrow2622K04P076Input 20 = momentScalarGrow2622K04P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P076] using h

theorem momentScalarGrow2622K04P076_radius_le :
    (momentScalarGrow2622K04P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P076Expected]

end ConnesWeilRH.Dev
