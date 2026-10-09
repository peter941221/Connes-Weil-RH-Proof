import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P042 : ℚ := ((-15048522019868554757214065855500710537300578203067937 : ℚ) / 377250110136039315761326147444890554448687587655680)

def momentPanelGrowth2622K00P042 : ℚ := ((269686068042961448986639840064026281871977988966527031 : ℚ) / 528335125491429734466441760284487430797837826680422400)

theorem momentPanelPhase_owner2622K00P042 :
    (momentPanelPhase2622K00P042 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-19 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P042 :
    (momentPanelGrowth2622K00P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P042Input : RatPair2542 := (momentPanelPhase2622K00P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P042Expected : RatState2542 :=
  ((((10129180622849794461014442545012165327458493562122127223639786485111157842347047 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12840752794132070647618184947619 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P042_replay :
    compactExp2620 momentScalarAmp2622K00P042Input 20 = momentScalarAmp2622K00P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K00P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P042_replay] at h
  simpa only [momentPanelPhase_owner2622K00P042] using h

theorem momentScalarAmp2622K00P042_radius_le :
    (momentScalarAmp2622K00P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622K00P042Expected]

def momentScalarGrow2622K00P042Input : RatPair2542 := (momentPanelGrowth2622K00P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P042Expected : RatState2542 :=
  ((((3558623941164142895704358273948109896370443417321394944402796831368582038526684828198043635790863 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2255544789505847949724102773860144134641780877049 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P042_replay :
    compactExp2620 momentScalarGrow2622K00P042Input 20 = momentScalarGrow2622K00P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P042] using h

theorem momentScalarGrow2622K00P042_radius_le :
    (momentScalarGrow2622K00P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P042Expected]

end ConnesWeilRH.Dev
