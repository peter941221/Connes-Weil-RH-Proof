import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P016 : ℚ := ((-379079552550680960564505608038433502514755859803638379 : ℚ) / 5249702463311061634508587452829133010643018632396800)

def momentPanelGrowth2622K04P016 : ℚ := ((137783444257092676510737317545718115798955268241591949 : ℚ) / 60855986194981611580479937965566188271683018476748800)

theorem momentPanelPhase_owner2622K04P016 :
    (momentPanelPhase2622K04P016 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-147 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P016 :
    (momentPanelGrowth2622K04P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P016Input : RatPair2542 := (momentPanelPhase2622K04P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P016Expected : RatState2542 :=
  ((((46589178534828147547728668369043649077913465309845514141472220715 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851757354994023302273 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P016_replay :
    compactExp2620 momentScalarAmp2622K04P016Input 20 = momentScalarAmp2622K04P016Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622K04P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P016]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P016 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P016_replay] at h
  simpa only [momentPanelPhase_owner2622K04P016] using h

theorem momentScalarAmp2622K04P016_radius_le :
    (momentScalarAmp2622K04P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P016Expected]

def momentScalarGrow2622K04P016Input : RatPair2542 := (momentPanelGrowth2622K04P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P016Expected : RatState2542 :=
  ((((10276625105714493481676463943698474842537508344324374606357960566105446915609438013731144433086995 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((26054283710566104651200932678626097438894071519451 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P016_replay :
    compactExp2620 momentScalarGrow2622K04P016Input 20 = momentScalarGrow2622K04P016Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P016_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P016] using h

theorem momentScalarGrow2622K04P016_radius_le :
    (momentScalarGrow2622K04P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P016Expected]

end ConnesWeilRH.Dev
