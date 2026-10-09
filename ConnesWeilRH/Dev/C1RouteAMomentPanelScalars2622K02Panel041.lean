import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P041 : ℚ := ((-119951491923352103827900346859395800474944592654698011 : ℚ) / 2910728944504534581430268406095300381138973464985600)

def momentPanelGrowth2622K02P041 : ℚ := ((1511020764915665162780951368326382699330501209233232293 : ℚ) / 2747204466433826828189813090231772540029652121210060800)

theorem momentPanelPhase_owner2622K02P041 :
    (momentPanelPhase2622K02P041 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-97 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P041, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P041 :
    (momentPanelGrowth2622K02P041 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P041, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P041Input : RatPair2542 := (momentPanelPhase2622K02P041 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P041Expected : RatState2542 :=
  ((((1352821446435295851688915643852992940675542393291160114824485482006005003059929 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3429947052723966504305721865561 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P041_replay :
    compactExp2620 momentScalarAmp2622K02P041Input 20 = momentScalarAmp2622K02P041Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P041_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-97 / 200) 0) -
      (momentScalarAmp2622K02P041Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P041]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P041 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P041 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P041Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P041_replay] at h
  simpa only [momentPanelPhase_owner2622K02P041] using h

theorem momentScalarAmp2622K02P041_radius_le :
    (momentScalarAmp2622K02P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P041Expected]

def momentScalarGrow2622K02P041Input : RatPair2542 := (momentPanelGrowth2622K02P041 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P041Expected : RatState2542 :=
  ((((3702284554892806883631956281752765455298414470143623183964596931170519205114866507355363653422611 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2346600388224077064590158176908537262688115071177 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P041_replay :
    compactExp2620 momentScalarGrow2622K02P041Input 20 = momentScalarGrow2622K02P041Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P041_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P041Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P041Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P041 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P041]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P041 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P041 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P041Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P041Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P041_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P041] using h

theorem momentScalarGrow2622K02P041_radius_le :
    (momentScalarGrow2622K02P041Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P041Expected]

end ConnesWeilRH.Dev
