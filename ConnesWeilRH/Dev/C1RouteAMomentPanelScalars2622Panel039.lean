import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P039 : ℚ := ((-1882300414869930740447579849052228593976423802018590743 : ℚ) / 45365924261274558395366254510533872607007431091814400)

def momentPanelGrowth2622P039 : ℚ := ((72902432628809651017816355233940216141072483844027185671 : ℚ) / 125015938902358412138355132980787952943673402980722278400)

theorem momentPanelPhase_owner2622P039 :
    (momentPanelPhase2622P039 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-101 / 200) 0 := by
  norm_num [momentPanelPhase2622P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P039 :
    (momentPanelGrowth2622P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P039Input : RatPair2542 := (momentPanelPhase2622P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P039Expected : RatState2542 :=
  ((((2042055327180014116273528768537196892719951798950818610787600021048774200294043 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1294358755439499741244713761755 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P039_replay :
    compactExp2620 momentScalarAmp2622P039Input 20 = momentScalarAmp2622P039Expected := by
  decide +kernel

theorem momentScalarAmp2622P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P039]
  have h := compactExp_real_error2620 momentPanelPhase2622P039 20 hsmall
  change |Real.exp (momentPanelPhase2622P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P039_replay] at h
  simpa only [momentPanelPhase_owner2622P039] using h

theorem momentScalarAmp2622P039_radius_le :
    (momentScalarAmp2622P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622P039Expected]

def momentScalarGrow2622P039Input : RatPair2542 := (momentPanelGrowth2622P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P039Expected : RatState2542 :=
  ((((956743062437738053337283382833353628639916582149843273676103835625199074183779156723577942489115 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4851260971518593687137408279039211150609892145581 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P039_replay :
    compactExp2620 momentScalarGrow2622P039Input 20 = momentScalarGrow2622P039Expected := by
  decide +kernel

theorem momentScalarGrow2622P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P039_replay] at h
  simpa only [momentPanelGrowth_owner2622P039] using h

theorem momentScalarGrow2622P039_radius_le :
    (momentScalarGrow2622P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P039Expected]

end ConnesWeilRH.Dev
