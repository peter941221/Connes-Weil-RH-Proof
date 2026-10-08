import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P129 : ℚ := ((-102164296334779458692459298837241721235106321811817851 : ℚ) / 3212163657204033308309778402843033753943009551974400)

def momentPanelGrowth2622K04P129 : ℚ := ((9123085633409120220392129938082920724755159363469 : ℚ) / 20980541082777610251556803750907578504826375372800)

theorem momentPanelPhase_owner2622K04P129 :
    (momentPanelPhase2622K04P129 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P129 :
    (momentPanelGrowth2622K04P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P129Input : RatPair2542 := (momentPanelPhase2622K04P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P129Expected : RatState2542 :=
  ((((32860117384693024024171061027237230962965975644967904507175432638252614846387572009 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((41656411033313713096669715592044423 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P129_replay :
    compactExp2620 momentScalarAmp2622K04P129Input 20 = momentScalarAmp2622K04P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K04P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P129_replay] at h
  simpa only [momentPanelPhase_owner2622K04P129] using h

theorem momentScalarAmp2622K04P129_radius_le :
    (momentScalarAmp2622K04P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P129Expected]

def momentScalarGrow2622K04P129Input : RatPair2542 := (momentPanelGrowth2622K04P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P129Expected : RatState2542 :=
  ((((3299478501631862243311758910404403632662280867495088905601095828386058689395180493063292932058249 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4182584168551226617299101800007644857946469151187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P129_replay :
    compactExp2620 momentScalarGrow2622K04P129Input 20 = momentScalarGrow2622K04P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P129] using h

theorem momentScalarGrow2622K04P129_radius_le :
    (momentScalarGrow2622K04P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P129Expected]

end ConnesWeilRH.Dev
