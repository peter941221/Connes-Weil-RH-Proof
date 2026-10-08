import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P020 : ℚ := ((-127129828466374504869764839977265001744378418371538929 : ℚ) / 1967603669164436292026953037483073995017254495846400)

def momentPanelGrowth2622K04P020 : ℚ := ((211533020490979765298447838299489392917690082142909 : ℚ) / 123742374957606721687753393551271228324384132300800)

theorem momentPanelPhase_owner2622K04P020 :
    (momentPanelPhase2622K04P020 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-139 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P020, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P020 :
    (momentPanelGrowth2622K04P020 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P020, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P020Input : RatPair2542 := (momentPanelPhase2622K04P020 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P020Expected : RatState2542 :=
  ((((92928690483337623259181143404061895573536666220016538692614260913755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2418087255967705369599737 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P020_replay :
    compactExp2620 momentScalarAmp2622K04P020Input 20 = momentScalarAmp2622K04P020Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P020_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-139 / 200) 0) -
      (momentScalarAmp2622K04P020Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P020]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P020 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P020 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P020Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P020_replay] at h
  simpa only [momentPanelPhase_owner2622K04P020] using h

theorem momentScalarAmp2622K04P020_radius_le :
    (momentScalarAmp2622K04P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P020Expected]

def momentScalarGrow2622K04P020Input : RatPair2542 := (momentPanelGrowth2622K04P020 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P020Expected : RatState2542 :=
  ((((11803450739056232941806393118564883295029418328787586019595432915895580280703519139183273647525661 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14962627020971767048314526882254805629678126601351 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P020_replay :
    compactExp2620 momentScalarGrow2622K04P020Input 20 = momentScalarGrow2622K04P020Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P020_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P020Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P020Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P020 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P020]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P020 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P020 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P020Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P020Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P020_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P020] using h

theorem momentScalarGrow2622K04P020_radius_le :
    (momentScalarGrow2622K04P020Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P020Expected]

end ConnesWeilRH.Dev
