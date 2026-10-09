import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P098 : ℚ := ((-31714876109854421106946878240355048825 : ℚ) / 1073913023694148645607159061091975168)

def momentPanelGrowth2622K07P098 : ℚ := ((541270068802617224194141200663752658075 : ℚ) / 3991033059393321789835164198867883261952)

theorem momentPanelPhase_owner2622K07P098 :
    (momentPanelPhase2622K07P098 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P098 :
    (momentPanelGrowth2622K07P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P098Input : RatPair2542 := (momentPanelPhase2622K07P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P098Expected : RatState2542 :=
  ((((19946328849775848846242808849187768999401303861237403961007024303289045123265321167 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((404571005991172524433827098098623261 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P098_replay :
    compactExp2620 momentScalarAmp2622K07P098Input 20 = momentScalarAmp2622K07P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K07P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P098_replay] at h
  simpa only [momentPanelPhase_owner2622K07P098] using h

theorem momentScalarAmp2622K07P098_radius_le :
    (momentScalarAmp2622K07P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P098Expected]

def momentScalarGrow2622K07P098Input : RatPair2542 := (momentPanelGrowth2622K07P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P098Expected : RatState2542 :=
  ((((611558926535098188286590244296928665525463449443906232408409688947934998244252033285635622304093 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3100971760112652878872020794259946153130033164567 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P098_replay :
    compactExp2620 momentScalarGrow2622K07P098Input 20 = momentScalarGrow2622K07P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P098] using h

theorem momentScalarGrow2622K07P098_radius_le :
    (momentScalarGrow2622K07P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P098Expected]

end ConnesWeilRH.Dev
