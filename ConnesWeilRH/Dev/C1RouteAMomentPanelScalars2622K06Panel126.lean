import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P126 : ℚ := ((-19156339 : ℚ) / 577850)

def momentPanelGrowth2622K06P126 : ℚ := ((209831387 : ℚ) / 620784675)

theorem momentPanelPhase_owner2622K06P126 :
    (momentPanelPhase2622K06P126 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (73 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P126 :
    (momentPanelGrowth2622K06P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P126Input : RatPair2542 := (momentPanelPhase2622K06P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P126Expected : RatState2542 :=
  ((((534757605449950509637338074326015305228456848958050816941121657335646884495701689 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((10846515705387782578024285503240503 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P126_replay :
    compactExp2620 momentScalarAmp2622K06P126Input 20 = momentScalarAmp2622K06P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K06P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P126_replay] at h
  simpa only [momentPanelPhase_owner2622K06P126] using h

theorem momentScalarAmp2622K06P126_radius_le :
    (momentScalarAmp2622K06P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P126Expected]

def momentScalarGrow2622K06P126Input : RatPair2542 := (momentPanelGrowth2622K06P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P126Expected : RatState2542 :=
  ((((748745922428288197151135916740241270031204735515187941514567678118863855128302911144592640044329 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3796591648101832805958472093128716375380098478613 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P126_replay :
    compactExp2620 momentScalarGrow2622K06P126Input 20 = momentScalarGrow2622K06P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P126] using h

theorem momentScalarGrow2622K06P126_radius_le :
    (momentScalarGrow2622K06P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P126Expected]

end ConnesWeilRH.Dev
