import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P074 : ℚ := ((-119632197109475618068159936867138461499853470538327381 : ℚ) / 3714554845036531186442295064089256041949736363622400)

def momentPanelGrowth2622K04P074 : ℚ := ((3454998085750958656822546238204478201508072750757429 : ℚ) / 17644635050615970221559271954513273522558981688524800)

theorem momentPanelPhase_owner2622K04P074 :
    (momentPanelPhase2622K04P074 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P074 :
    (momentPanelGrowth2622K04P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P074Input : RatPair2542 := (momentPanelPhase2622K04P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P074Expected : RatState2542 :=
  ((((22007216222997075973351400828961553505291238396664811556047192759406991181148609245 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((27898317722509909647730716335670135 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P074_replay :
    compactExp2620 momentScalarAmp2622K04P074Input 20 = momentScalarAmp2622K04P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K04P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P074_replay] at h
  simpa only [momentPanelPhase_owner2622K04P074] using h

theorem momentScalarAmp2622K04P074_radius_le :
    (momentScalarAmp2622K04P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P074Expected]

def momentScalarGrow2622K04P074Input : RatPair2542 := (momentPanelGrowth2622K04P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P074Expected : RatState2542 :=
  ((((2597992341946742183240941196757624689650978098724101503670353294298959926068395889354610201144067 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1646672968330339729753145231211469763272613284869 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P074_replay :
    compactExp2620 momentScalarGrow2622K04P074Input 20 = momentScalarGrow2622K04P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P074] using h

theorem momentScalarGrow2622K04P074_radius_le :
    (momentScalarGrow2622K04P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P074Expected]

end ConnesWeilRH.Dev
