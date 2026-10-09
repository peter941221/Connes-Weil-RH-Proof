import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P082 : ℚ := ((-2768167113118916593434230586053958307635593913741867 : ℚ) / 90830043163807286830549319095765870479397995151360)

def momentPanelGrowth2622K02P082 : ℚ := ((1642130858411194266081086186806964437648448716502413 : ℚ) / 18346840915427302483039948651482425129659293027532800)

theorem momentPanelPhase_owner2622K02P082 :
    (momentPanelPhase2622K02P082 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P082, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P082 :
    (momentPanelGrowth2622K02P082 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-3 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P082, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P082Input : RatPair2542 := (momentPanelPhase2622K02P082 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P082Expected : RatState2542 :=
  ((((31033668545441232550576565063841960672542183242452328528954937973802805743035201003 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((157363967876802083344566647900082887 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P082_replay :
    compactExp2620 momentScalarAmp2622K02P082Input 20 = momentScalarAmp2622K02P082Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P082_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 40) 0) -
      (momentScalarAmp2622K02P082Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P082]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P082 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P082 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P082Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P082_replay] at h
  simpa only [momentPanelPhase_owner2622K02P082] using h

theorem momentScalarAmp2622K02P082_radius_le :
    (momentScalarAmp2622K02P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P082Expected]

def momentScalarGrow2622K02P082Input : RatPair2542 := (momentPanelGrowth2622K02P082 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P082Expected : RatState2542 :=
  ((((2335985086475929515250499690086601866193940216598768595726956067529210082288155738708071978698619 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2961212644230852734790986294691060647795358601219 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P082_replay :
    compactExp2620 momentScalarGrow2622K02P082Input 20 = momentScalarGrow2622K02P082Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P082_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-3 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P082Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P082Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P082 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P082]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P082 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P082 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P082Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P082Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P082_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P082] using h

theorem momentScalarGrow2622K02P082_radius_le :
    (momentScalarGrow2622K02P082Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P082Expected]

end ConnesWeilRH.Dev
