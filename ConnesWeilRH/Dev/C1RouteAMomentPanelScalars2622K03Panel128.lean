import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P128 : ℚ := ((-72838613890717384819823858783113616932798781436910175 : ℚ) / 2074784261895883055254906080644853281779053236322304)

def momentPanelGrowth2622K03P128 : ℚ := ((2156886636665027933560130249106604950944792023018720425 : ℚ) / 6567023858428291651662777593967685188308476661151563776)

theorem momentPanelPhase_owner2622K03P128 :
    (momentPanelPhase2622K03P128 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P128 :
    (momentPanelGrowth2622K03P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P128Input : RatPair2542 := (momentPanelPhase2622K03P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P128Expected : RatState2542 :=
  ((((302647775531592515832565721013728261204403441537943549275370333288566680784541261 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1534657919544360408258225949303405 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P128_replay :
    compactExp2620 momentScalarAmp2622K03P128Input 20 = momentScalarAmp2622K03P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K03P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P128_replay] at h
  simpa only [momentPanelPhase_owner2622K03P128] using h

theorem momentScalarAmp2622K03P128_radius_le :
    (momentScalarAmp2622K03P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P128Expected]

def momentScalarGrow2622K03P128Input : RatPair2542 := (momentPanelGrowth2622K03P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P128Expected : RatState2542 :=
  ((((2966464620086809642462984799431126701975877710925692832098003415118907294876701719499627318345135 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3760439478338516756046625013323476436558368375569 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P128_replay :
    compactExp2620 momentScalarGrow2622K03P128Input 20 = momentScalarGrow2622K03P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P128] using h

theorem momentScalarGrow2622K03P128_radius_le :
    (momentScalarGrow2622K03P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P128Expected]

end ConnesWeilRH.Dev
