import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P177 : ℚ := ((-1366889867336649546056032447438404684282531293287 : ℚ) / 11417981541647679048466287755595961091061972992)

def momentPanelGrowth2622K04P177 : ℚ := ((9901898201603748053307500662427636166705601623098429 : ℚ) / 945837045956239613177326111954180426880846187724800)

theorem momentPanelPhase_owner2622K04P177 :
    (momentPanelPhase2622K04P177 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P177 :
    (momentPanelGrowth2622K04P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P177Input : RatPair2542 := (momentPanelPhase2622K04P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P177Expected : RatState2542 :=
  ((((54512907708351508529377458359846011613232093 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P177_replay :
    compactExp2620 momentScalarAmp2622K04P177Input 20 = momentScalarAmp2622K04P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K04P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P177_replay] at h
  simpa only [momentPanelPhase_owner2622K04P177] using h

theorem momentScalarAmp2622K04P177_radius_le :
    (momentScalarAmp2622K04P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P177Expected]

def momentScalarGrow2622K04P177Input : RatPair2542 := (momentPanelGrowth2622K04P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P177Expected : RatState2542 :=
  ((((75196128079890819270402167014138033801039709441759183674820924083099426536246312637028910065325529167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((47660732603099829720702020699751369851016111314007077 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P177_replay :
    compactExp2620 momentScalarGrow2622K04P177Input 20 = momentScalarGrow2622K04P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P177] using h

theorem momentScalarGrow2622K04P177_radius_le :
    (momentScalarGrow2622K04P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P177Expected]

end ConnesWeilRH.Dev
