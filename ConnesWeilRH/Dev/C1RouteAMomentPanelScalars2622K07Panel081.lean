import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P081 : ℚ := ((-33188834621830924249684325874896151175 : ℚ) / 1073913023694148645607159061091975168)

def momentPanelGrowth2622K07P081 : ℚ := ((541270068802617224194141200663752658075 : ℚ) / 3991033059393321789835164198867883261952)

theorem momentPanelPhase_owner2622K07P081 :
    (momentPanelPhase2622K07P081 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P081 :
    (momentPanelGrowth2622K07P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P081Input : RatPair2542 := (momentPanelPhase2622K07P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P081Expected : RatState2542 :=
  ((((20223139527612738395135001456531938360373923371004666701587540406433002804558562877 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((51273261072373727263228433914970787 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P081_replay :
    compactExp2620 momentScalarAmp2622K07P081Input 20 = momentScalarAmp2622K07P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K07P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P081_replay] at h
  simpa only [momentPanelPhase_owner2622K07P081] using h

theorem momentScalarAmp2622K07P081_radius_le :
    (momentScalarAmp2622K07P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P081Expected]

def momentScalarGrow2622K07P081Input : RatPair2542 := (momentPanelGrowth2622K07P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P081Expected : RatState2542 :=
  ((((611558926535098188286590244296928665525463449443906232408409688947934998244252033285635622304093 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3100971760112652878872020794259946153130033164567 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P081_replay :
    compactExp2620 momentScalarGrow2622K07P081Input 20 = momentScalarGrow2622K07P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P081] using h

theorem momentScalarGrow2622K07P081_radius_le :
    (momentScalarGrow2622K07P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P081Expected]

end ConnesWeilRH.Dev
