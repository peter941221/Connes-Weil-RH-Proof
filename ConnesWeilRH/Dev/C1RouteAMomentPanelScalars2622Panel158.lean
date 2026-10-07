import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P158 : ℚ := ((-1773314543016866641651955846249952532504751809074538421 : ℚ) / 32322022148096249850398367378541046656578233145753600)

def momentPanelGrowth2622P158 : ℚ := ((96057196829084216466054741288898688150782532902442109991 : ℚ) / 62678144189874077242483812889732154235533998242031206400)

theorem momentPanelPhase_owner2622P158 :
    (momentPanelPhase2622P158 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (137 / 200) 0 := by
  norm_num [momentPanelPhase2622P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P158 :
    (momentPanelGrowth2622P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P158Input : RatPair2542 := (momentPanelPhase2622P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P158Expected : RatState2542 :=
  ((((3180372452076801047761461399318628530606737474548620177118375690189326935 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6449663635466616712276381 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P158_replay :
    compactExp2620 momentScalarAmp2622P158Input 20 = momentScalarAmp2622P158Expected := by
  decide +kernel

theorem momentScalarAmp2622P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P158]
  have h := compactExp_real_error2620 momentPanelPhase2622P158 20 hsmall
  change |Real.exp (momentPanelPhase2622P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P158_replay] at h
  simpa only [momentPanelPhase_owner2622P158] using h

theorem momentScalarAmp2622P158_radius_le :
    (momentScalarAmp2622P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [momentScalarAmp2622P158Expected]

def momentScalarGrow2622P158Input : RatPair2542 := (momentPanelGrowth2622P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P158Expected : RatState2542 :=
  ((((9657735931470978617976015774938198109567023141116342680738010055552323922867335079515309485951 : ℚ) / 2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024), 0), ((12536439661729168544957978140090974126015754605115 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P158_replay :
    compactExp2620 momentScalarGrow2622P158Input 20 = momentScalarGrow2622P158Expected := by
  decide +kernel

theorem momentScalarGrow2622P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P158_replay] at h
  simpa only [momentPanelGrowth_owner2622P158] using h

theorem momentScalarGrow2622P158_radius_le :
    (momentScalarGrow2622P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P158Expected]

end ConnesWeilRH.Dev
