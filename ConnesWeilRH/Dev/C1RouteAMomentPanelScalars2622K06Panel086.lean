import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P086 : ℚ := ((-20093219 : ℚ) / 665850)

def momentPanelGrowth2622K06P086 : ℚ := ((207917 : ℚ) / 3244800)

theorem momentPanelPhase_owner2622K06P086 :
    (momentPanelPhase2622K06P086 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-7 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P086, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P086 :
    (momentPanelGrowth2622K06P086 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P086, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P086Input : RatPair2542 := (momentPanelPhase2622K06P086 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P086Expected : RatState2542 :=
  ((((5233991969958923621035267774093266549590151528804639390899312455812139121103840349 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((212322048289425059386959873890802089 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P086_replay :
    compactExp2620 momentScalarAmp2622K06P086Input 20 = momentScalarAmp2622K06P086Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P086_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-7 / 200) 0) -
      (momentScalarAmp2622K06P086Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P086]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P086 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P086 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P086Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P086_replay] at h
  simpa only [momentPanelPhase_owner2622K06P086] using h

theorem momentScalarAmp2622K06P086_radius_le :
    (momentScalarAmp2622K06P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P086Expected]

def momentScalarGrow2622K06P086Input : RatPair2542 := (momentPanelGrowth2622K06P086 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P086Expected : RatState2542 :=
  ((((569333714018170166295400027413786033070029452605243348211905099049771352948160419525531513960819 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1443432360404504294077847275475724421924525736933 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P086_replay :
    compactExp2620 momentScalarGrow2622K06P086Input 20 = momentScalarGrow2622K06P086Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P086_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P086Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P086]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P086 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P086 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P086Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P086_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P086] using h

theorem momentScalarGrow2622K06P086_radius_le :
    (momentScalarGrow2622K06P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P086Expected]

end ConnesWeilRH.Dev
