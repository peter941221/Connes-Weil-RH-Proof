import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P073 : ℚ := ((-359894799565734795425421627638888588296798579599915201 : ℚ) / 11107126994176320986371793071449861050357810777292800)

def momentPanelGrowth2622K04P073 : ℚ := ((910131979258133157638243506553423129004923737468231189 : ℚ) / 4486482758709934482284585771466194101108940343135436800)

theorem momentPanelPhase_owner2622K04P073 :
    (momentPanelPhase2622K04P073 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P073 :
    (momentPanelGrowth2622K04P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P073Input : RatPair2542 := (momentPanelPhase2622K04P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P073Expected : RatState2542 :=
  ((((4523384372164962424599264990557942365936429886947884987653697414905719199597614957 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5734248106871054751356600650902089 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P073_replay :
    compactExp2620 momentScalarAmp2622K04P073Input 20 = momentScalarAmp2622K04P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K04P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P073_replay] at h
  simpa only [momentPanelPhase_owner2622K04P073] using h

theorem momentScalarAmp2622K04P073_radius_le :
    (momentScalarAmp2622K04P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P073Expected]

def momentScalarGrow2622K04P073Input : RatPair2542 := (momentPanelGrowth2622K04P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P073Expected : RatState2542 :=
  ((((2616374975742534941187794537308785583720069093461480266019716151691160458636679084791870148992329 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3316648666772482722983945710608494709234242793907 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P073_replay :
    compactExp2620 momentScalarGrow2622K04P073Input 20 = momentScalarGrow2622K04P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P073] using h

theorem momentScalarGrow2622K04P073_radius_le :
    (momentScalarGrow2622K04P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P073Expected]

end ConnesWeilRH.Dev
