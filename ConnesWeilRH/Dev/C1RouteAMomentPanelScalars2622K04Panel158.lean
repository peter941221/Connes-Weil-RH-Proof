import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P158 : ℚ := ((-101075422989882738668607988628276516313056043029325677 : ℚ) / 2020126384256015615649897961158815416036139571609600)

def momentPanelGrowth2622K04P158 : ℚ := ((6279779833382165566151967468472416335234903063612170767 : ℚ) / 3917384011867129827655238305608259639720874890126950400)

theorem momentPanelPhase_owner2622K04P158 :
    (momentPanelPhase2622K04P158 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (137 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P158 :
    (momentPanelGrowth2622K04P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P158Input : RatPair2542 := (momentPanelPhase2622K04P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P158Expected : RatState2542 :=
  ((((398123967624139210436731887293423387572684266398726766386089470223590762809 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((253562010159623416706453881 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P158_replay :
    compactExp2620 momentScalarAmp2622K04P158Input 20 = momentScalarAmp2622K04P158Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622K04P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P158]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P158 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P158_replay] at h
  simpa only [momentPanelPhase_owner2622K04P158] using h

theorem momentScalarAmp2622K04P158_radius_le :
    (momentScalarAmp2622K04P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P158Expected]

def momentScalarGrow2622K04P158Input : RatPair2542 := (momentPanelGrowth2622K04P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P158Expected : RatState2542 :=
  ((((2652994310572967108790650815268918111282855214456622421277283045911793097156693250632393170927657 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((13452258755080366020401721908231339621698692977173 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P158_replay :
    compactExp2620 momentScalarGrow2622K04P158Input 20 = momentScalarGrow2622K04P158Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P158_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P158] using h

theorem momentScalarGrow2622K04P158_radius_le :
    (momentScalarGrow2622K04P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P158Expected]

end ConnesWeilRH.Dev
